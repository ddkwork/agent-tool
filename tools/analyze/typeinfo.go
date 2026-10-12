package analyze

import (
	"debug/dwarf"
	"debug/elf"
	"debug/pe"
	"errors"
	"fmt"
	"sort"
	"strings"
	"sync"

	"agent-tool/common"

	"github.com/knewstimek/gopdb"
	"github.com/knewstimek/gosleigh/pkg/pcode"
)

const (
	// typeSectionBudget bounds the definitions printed after a decompiled
	// function. The engine's own list is the transitive closure of every
	// type reachable from the parameters -- dozens of large C++ classes --
	// so only the types the C text names are printed, up to this size.
	typeSectionBudget = 6000
	// typeSectionMembers is the member cap per structure in that section;
	// type_info prints the rest.
	typeSectionMembers = 32
	typeInfoMembers    = 1024
	typeInfoMaxNames   = 16
	typeInfoMaxMatches = 8
)

// typeIndex maps the names of a debug source's structures, unions, enums
// (and typedefs, as aliases) to the source's reference for each.
type typeIndex struct {
	refs      map[string]typeRef  // qualified name -> definition
	byDisplay map[string]string   // ghidraName(qualified) -> qualified
	byShort   map[string][]string // name as the decompiler prints it -> qualified names
	// enumerators maps an enumerator to its enums: a body that compares
	// against MODE_AUTO names no type, yet needs the enum to read 0x20.
	enumerators map[string][]string
}

type typeRef struct {
	ref   uint64 // pdb.TypeIndex or dwarf.Offset
	alias bool   // a typedef: a tag of the same name wins
}

func newTypeIndex() *typeIndex {
	return &typeIndex{refs: map[string]typeRef{}, byDisplay: map[string]string{}, byShort: map[string][]string{},
		enumerators: map[string][]string{}}
}

func (x *typeIndex) addEnumerator(name, enum string) {
	for _, e := range x.enumerators[name] {
		if e == enum {
			return
		}
	}
	x.enumerators[name] = append(x.enumerators[name], enum)
}

func (x *typeIndex) add(qual string, ref uint64, alias bool) {
	if qual == "" || qual[0] == '<' || strings.Contains(qual, "<unnamed") || strings.Contains(qual, "__unnamed") {
		return
	}
	old, existed := x.refs[qual]
	if existed && (alias || !old.alias) {
		return
	}
	x.refs[qual] = typeRef{ref, alias}
	if !existed {
		x.byDisplay[ghidraName(qual)] = qual
		short := typeName(qual)
		x.byShort[short] = append(x.byShort[short], qual)
	}
}

var typeTagWords = strings.NewReplacer("struct ", "", "class ", "", "union ", "", "enum ", "")

// find returns the qualified names name stands for: the qualified name
// itself, its display form, or the short name the decompiler prints (which
// can name types in several namespaces). fold adds a case-insensitive pass
// when nothing matches exactly.
func (x *typeIndex) find(name string, fold bool) []string {
	n := ghidraName(strings.TrimSpace(typeTagWords.Replace(name)))
	set := map[string]bool{}
	if q, ok := x.byDisplay[n]; ok {
		set[q] = true
	}
	for _, q := range x.byShort[n] {
		set[q] = true
	}
	if len(set) == 0 && fold {
		for d, q := range x.byDisplay {
			if strings.EqualFold(d, n) {
				set[q] = true
			}
		}
		for s, qs := range x.byShort {
			if strings.EqualFold(s, n) {
				for _, q := range qs {
					set[q] = true
				}
			}
		}
	}
	return sortedKeys(set)
}

// similar lists up to n type names containing name, shortest first.
func (x *typeIndex) similar(name string, n int) []string {
	sub := strings.ToLower(ghidraName(strings.TrimSpace(typeTagWords.Replace(name))))
	if sub == "" {
		return nil
	}
	var out, near []string
	for d, q := range x.byDisplay {
		dl := strings.ToLower(d)
		switch {
		case strings.Contains(dl, sub):
			out = append(out, q)
		case nearName(strings.ToLower(typeName(q)), sub):
			near = append(near, q)
		}
	}
	if len(out) == 0 {
		out = near // a typo: Colr for Color
	}
	sort.Slice(out, func(i, j int) bool {
		if len(out[i]) != len(out[j]) {
			return len(out[i]) < len(out[j])
		}
		return out[i] < out[j]
	})
	if len(out) > n {
		out = out[:n]
	}
	return out
}

// nearName reports names within a small edit distance (one edit per four
// characters, at least one), for suggestions after a typo.
func nearName(a, b string) bool {
	limit := max(1, len(b)/4)
	if d := len(a) - len(b); d > limit || -d > limit {
		return false
	}
	prev := make([]int, len(b)+1)
	cur := make([]int, len(b)+1)
	for j := range prev {
		prev[j] = j
	}
	for i := 1; i <= len(a); i++ {
		cur[0] = i
		best := cur[0]
		for j := 1; j <= len(b); j++ {
			cost := 1
			if a[i-1] == b[j-1] {
				cost = 0
			}
			cur[j] = min(prev[j]+1, cur[j-1]+1, prev[j-1]+cost)
			best = min(best, cur[j])
		}
		if best > limit {
			return false
		}
		prev, cur = cur, prev
	}
	return prev[len(b)] <= limit
}

func sortedKeys(set map[string]bool) []string {
	out := make([]string, 0, len(set))
	for k := range set {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

// --- PDB ---

func (pi *pdbInfo) typeIndex() *typeIndex { return pi.types.typeIndex() }

func (pi *pdbInfo) typeDesc(ref uint64) *pcode.HostTypeDesc {
	return pi.types.desc(pdb.TypeIndex(ref))
}

func (pi *pdbInfo) overlapsOf(d *pcode.HostTypeDesc) []pcode.HostFieldDesc {
	return pi.types.overlaps[d]
}

func (c *pdbTypes) typeIndex() *typeIndex {
	if c.index != nil {
		return c.index
	}
	x := newTypeIndex()
	// The type table already decodes every definition's name once (for
	// forward-reference resolution); only enums are decoded again, for their
	// enumerators.
	for _, def := range c.tt.Definitions() {
		x.add(def.Name, uint64(def.Index), false)
		if def.Leaf != pdb.LFEnum {
			continue
		}
		if v, err := c.tt.Lookup(def.Index); err == nil {
			if e, ok := v.(*pdb.Enum); ok {
				fields, _ := c.tt.Fields(e.FieldList)
				for _, f := range fields {
					if en, ok := f.(*pdb.Enumerate); ok {
						x.addEnumerator(en.Name, def.Name)
					}
				}
			}
		}
	}
	c.index = x
	return x
}

// --- DWARF ---

func (di *dwarfInfo) typeDesc(ref uint64) *pcode.HostTypeDesc {
	t, err := di.d.Type(dwarf.Offset(ref))
	if err != nil {
		return nil
	}
	return di.desc(t)
}

func (di *dwarfInfo) overlapsOf(d *pcode.HostTypeDesc) []pcode.HostFieldDesc {
	return di.overlaps[d]
}

// typeIndex walks the DWARF once for the complete structure, class, union
// and enum definitions, qualified by their enclosing namespaces and types,
// and the typedefs (which name C's tagless structures).
func (di *dwarfInfo) typeIndex() *typeIndex {
	if di.index != nil {
		return di.index
	}
	x := newTypeIndex()
	r := di.d.Reader()
	var scopes []string // one per open children list; "" for an unnamed or function scope
	// The enumeration whose enumerators are being read, and the depth its
	// children list opened at. A tagless enum's enumerators wait in
	// anonEnums for the typedef that names it.
	var enum string
	var enumAnon dwarf.Offset
	enumDepth := -1
	anonEnums := map[dwarf.Offset][]string{}
	for {
		e, err := r.Next()
		if err != nil || e == nil {
			break
		}
		if e.Tag == 0 {
			if len(scopes) > 0 {
				scopes = scopes[:len(scopes)-1]
			}
			if len(scopes) < enumDepth {
				enumDepth = -1
			}
			continue
		}
		if e.Tag == dwarf.TagEnumerator && enumDepth >= 0 {
			if n, _ := e.Val(dwarf.AttrName).(string); n != "" {
				if enum != "" {
					x.addEnumerator(n, enum)
				} else {
					anonEnums[enumAnon] = append(anonEnums[enumAnon], n)
				}
			}
			continue
		}
		if e.Tag == dwarf.TagCompileUnit {
			scopes = scopes[:0]
		}
		name, _ := e.Val(dwarf.AttrName).(string)
		qual := func() string {
			var parts []string
			for _, s := range scopes {
				if s != "" {
					parts = append(parts, s)
				}
			}
			return strings.Join(append(parts, name), "::")
		}
		switch e.Tag {
		case dwarf.TagStructType, dwarf.TagClassType, dwarf.TagUnionType, dwarf.TagEnumerationType:
			if decl, _ := e.Val(dwarf.AttrDeclaration).(bool); name != "" && !decl {
				x.add(qual(), uint64(e.Offset), false)
			}
			if e.Tag == dwarf.TagEnumerationType && e.Children {
				enum, enumAnon, enumDepth = "", e.Offset, len(scopes)+1
				if name != "" {
					enum = qual()
				}
			}
		case dwarf.TagTypedef:
			if name != "" {
				q := qual()
				x.add(q, uint64(e.Offset), true)
				if to, ok := e.Val(dwarf.AttrType).(dwarf.Offset); ok {
					for _, n := range anonEnums[to] {
						x.addEnumerator(n, q)
					}
					delete(anonEnums, to)
				}
			}
		}
		if e.Children {
			scope := ""
			switch e.Tag {
			case dwarf.TagNamespace, dwarf.TagStructType, dwarf.TagClassType, dwarf.TagUnionType:
				scope = name
			}
			scopes = append(scopes, scope)
		}
	}
	di.index = x
	return x
}

// --- rendering ---

func isUDT(d *pcode.HostTypeDesc) bool {
	if d == nil {
		return false
	}
	switch d.Meta {
	case "struct", "union", "enum_int", "enum_uint":
		return true
	}
	return false
}

// cDecl declares name with type d the way the decompiler prints types.
func cDecl(d *pcode.HostTypeDesc, name string) string {
	join := func(t string) string {
		if name == "" {
			return t
		}
		return t + " " + name
	}
	switch {
	case d == nil:
		return join("undefined")
	case d.Typedef != "":
		return join(d.Typedef)
	case d.Meta == "ptr":
		return cDecl(d.Elem, "*"+name)
	case d.Meta == "array":
		if strings.HasPrefix(name, "*") {
			name = "(" + name + ")"
		}
		return cDecl(d.Elem, fmt.Sprintf("%s[%d]", name, d.Count))
	case d.Meta == "void":
		return join("void")
	case d.Name != "":
		return join(d.Name)
	case d.Meta == "code":
		return join("code")
	}
	if d.Size >= 1 && d.Size <= 8 {
		return join(fmt.Sprintf("undefined%d", d.Size))
	}
	return join(fmt.Sprintf("unkbyte%d", d.Size))
}

// enumValue prints an enumerator: decimal below 10, else hex with the
// decimal beside it, so it matches the constant however the body prints it.
func enumValue(v uint64, d *pcode.HostTypeDesc) string {
	if d.Meta == "enum_int" && d.Size > 0 && d.Size <= 8 {
		bits := uint(d.Size) * 8
		if s := int64(v<<(64-bits)) >> (64 - bits); s < 0 {
			return fmt.Sprintf("%d", s)
		}
	}
	if v < 10 {
		return fmt.Sprintf("%d", v)
	}
	return fmt.Sprintf("0x%x (%d)", v, v)
}

// renderType prints one definition: structures and unions with each
// member's offset (what a reverse engineer matches against [reg+off]),
// enums with their values. Members a layout had to leave out (an anonymous
// union's alternatives) are listed and marked.
func renderType(qual string, alias bool, d *pcode.HostTypeDesc, overlaps []pcode.HostFieldDesc, maxMembers int) string {
	var sb strings.Builder
	label := typeName(qual)
	where := ""
	if ghidraName(qual) != label {
		where = qual + ", "
	}
	switch {
	case d == nil:
		fmt.Fprintf(&sb, "// %s: no usable definition in the debug info\n", qual)
	case alias && !isUDT(d):
		under := *d
		under.Typedef = ""
		fmt.Fprintf(&sb, "typedef %s; // %s%d bytes\n", cDecl(&under, label), where, d.Size)
	case d.Meta == "enum_int" || d.Meta == "enum_uint":
		keys := make([]uint64, 0, len(d.EnumValues))
		for k := range d.EnumValues {
			keys = append(keys, k)
		}
		sort.Slice(keys, func(i, j int) bool { return keys[i] < keys[j] })
		parts := make([]string, 0, min(len(keys), maxMembers)+1)
		for i, k := range keys {
			if i == maxMembers {
				parts = append(parts, fmt.Sprintf("/* %d more: analyze type_info type_name=%s */", len(keys)-i, label))
				break
			}
			parts = append(parts, d.EnumValues[k]+" = "+enumValue(k, d))
		}
		fmt.Fprintf(&sb, "enum %s { %s }; // %s%d bytes\n", d.Name, strings.Join(parts, ", "), where, d.Size)
	case d.Meta == "struct" || d.Meta == "union":
		fmt.Fprintf(&sb, "%s %s { // %s0x%x bytes\n", d.Meta, d.Name, where, d.Size)
		type member struct {
			f       pcode.HostFieldDesc
			overlap bool
		}
		ms := make([]member, 0, len(d.Fields)+len(overlaps))
		for _, f := range d.Fields {
			ms = append(ms, member{f, false})
		}
		for _, f := range overlaps {
			ms = append(ms, member{f, true})
		}
		sort.SliceStable(ms, func(i, j int) bool {
			if ms[i].f.Offset != ms[j].f.Offset {
				return ms[i].f.Offset < ms[j].f.Offset
			}
			return ms[i].f.BitOffset < ms[j].f.BitOffset
		})
		for i, m := range ms {
			if i == maxMembers {
				fmt.Fprintf(&sb, "    // ... %d more members: analyze type_info type_name=%s\n", len(ms)-i, label)
				break
			}
			decl := cDecl(m.f.Type, m.f.Name)
			if m.f.BitSize > 0 {
				decl += fmt.Sprintf(" : %d", m.f.BitSize)
			}
			fmt.Fprintf(&sb, "    +0x%02x %s;", m.f.Offset, decl)
			if m.f.BitSize > 0 {
				fmt.Fprintf(&sb, " // bits %d..%d", m.f.BitOffset, m.f.BitOffset+m.f.BitSize-1)
			}
			if strings.HasPrefix(m.f.Name, "super_") {
				sb.WriteString(" // base class")
			}
			if m.overlap {
				sb.WriteString(" // overlaps an earlier member (union alternative); decompiled code names the earlier one")
			}
			sb.WriteString("\n")
		}
		sb.WriteString("};\n")
	default:
		fmt.Fprintf(&sb, "// %s: %s\n", qual, cDecl(d, ""))
	}
	return sb.String()
}

// typeSection lists the definitions of the structures, unions and enums the
// decompiled C names, within typeSectionBudget; those that do not fit are
// named so type_info can print them.
func typeSection(ds debugSource, c string) string {
	x := ds.typeIndex()
	seen := map[string]bool{}
	var sb strings.Builder
	var over, fieldEnums []string
	show := func(q string) {
		if seen[q] {
			return
		}
		seen[q] = true
		ref := x.refs[q]
		d := ds.typeDesc(ref.ref)
		if !isUDT(d) {
			return
		}
		s := renderType(q, ref.alias, d, ds.overlapsOf(d), typeSectionMembers)
		if sb.Len()+len(s) > typeSectionBudget {
			over = append(over, typeName(q))
			return
		}
		sb.WriteString(s)
		for _, f := range d.Fields {
			if f.Type != nil && (f.Type.Meta == "enum_int" || f.Type.Meta == "enum_uint") {
				if qs := x.find(f.Type.Name, false); len(qs) == 1 {
					fieldEnums = append(fieldEnums, qs[0])
				}
			}
		}
	}
	for _, tok := range typeTokens(c) {
		qs := x.find(tok, false)
		if len(qs) == 0 && len(x.enumerators[tok]) <= 2 {
			qs = x.enumerators[tok]
		}
		for _, q := range qs {
			show(q)
		}
	}
	// An enum a shown structure's member has is short and decodes the
	// constants stored into that member.
	for _, q := range fieldEnums {
		show(q)
	}
	if len(over) > 0 {
		fmt.Fprintf(&sb, "// not shown (size): %s -- analyze type_info type_name=<name>\n", strings.Join(over, ", "))
	}
	return sb.String()
}

// typeTokens returns the identifiers of c that can name a type, in order of
// first appearance: not a member after -> or ., not a called function, not
// inside a string or comment. A name with template arguments is returned
// whole as well as by its parts, a dotted Go name (main.T) whole.
func typeTokens(c string) []string {
	var out []string
	seen := map[string]bool{}
	emit := func(s string) {
		if s != "" && !seen[s] {
			seen[s] = true
			out = append(out, s)
		}
	}
	isID := func(b byte) bool {
		return b == '_' || b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' || b >= '0' && b <= '9'
	}
	for i := 0; i < len(c); {
		switch {
		case c[i] == '"':
			j := i + 1
			for j < len(c) && c[j] != '"' && c[j] != '\n' {
				if c[j] == '\\' {
					j++
				}
				j++
			}
			i = j + 1
			continue
		case strings.HasPrefix(c[i:], "/*"):
			if j := strings.Index(c[i+2:], "*/"); j >= 0 {
				i += j + 4
			} else {
				i = len(c)
			}
			continue
		case strings.HasPrefix(c[i:], "//"):
			if j := strings.IndexByte(c[i:], '\n'); j >= 0 {
				i += j
			} else {
				i = len(c)
			}
			continue
		case !isID(c[i]) || c[i] >= '0' && c[i] <= '9':
			i++
			continue
		}
		start := i
		for i < len(c) && isID(c[i]) {
			i++
		}
		word := c[start:i]
		member := start >= 1 && c[start-1] == '.' || start >= 2 && c[start-2:start] == "->"
		end := i
		// Template arguments, balanced, on one line.
		if end < len(c) && c[end] == '<' {
			depth := 0
			for k := end; k < len(c) && c[k] != '\n' && c[k] != ';' && c[k] != '{'; k++ {
				if c[k] == '<' {
					depth++
				} else if c[k] == '>' {
					if depth--; depth == 0 {
						emit(c[start : k+1])
						break
					}
				}
			}
		}
		// A dotted name (Go package.Type) is tried whole.
		for k := end; k+1 < len(c) && c[k] == '.' && isID(c[k+1]); {
			k++
			for k < len(c) && isID(c[k]) {
				k++
			}
			emit(c[start:k])
			end = k
		}
		if member {
			continue
		}
		if k := skipSpaces(c, i); k < len(c) && c[k] == '(' {
			continue
		}
		emit(word)
	}
	return out
}

func skipSpaces(s string, i int) int {
	for i < len(s) && (s[i] == ' ' || s[i] == '\t') {
		i++
	}
	return i
}

// globalDesc is the global variable whose storage contains va, with its
// type description.
func (pi *pdbInfo) globalDesc(va uint64) (string, uint64, *pcode.HostTypeDesc, bool) {
	d, ok := pi.globalAt(va)
	if !ok {
		return "", 0, nil, false
	}
	return d.name, d.va, pi.types.desc(d.typ), true
}

func (di *dwarfInfo) globalDesc(va uint64) (string, uint64, *pcode.HostTypeDesc, bool) {
	i := sort.Search(len(di.data), func(i int) bool { return di.data[i].va > va })
	if i == 0 || va >= di.data[i-1].va+di.data[i-1].size {
		return "", 0, nil, false
	}
	v := di.data[i-1]
	return v.name, v.va, di.desc(v.typ), true
}

// debugCache keeps the last debug source the server-side operations
// (type_info, struct_layout) opened: an agent asks about one binary several
// times in a row, and a large PDB takes seconds to load. The sources memoize
// lazily and are not safe for concurrent use, so callers hold mu throughout.
var debugCache struct {
	mu  sync.Mutex
	key string
	ds  debugSource
}

func init() {
	common.OnIdleRelease(func() {
		debugCache.mu.Lock()
		debugCache.key, debugCache.ds = "", nil
		debugCache.mu.Unlock()
	})
}

// withDebugInfo runs f on the binary's debug source (see openDebugInfo).
func withDebugInfo(path, pdbPath string, pdbForce bool, f func(debugSource) error) error {
	debugCache.mu.Lock()
	defer debugCache.mu.Unlock()
	key := fmt.Sprintf("%s|%s|%t", fileIdentity(path), pdbPath, pdbForce)
	if debugCache.ds == nil || debugCache.key != key {
		debugCache.key, debugCache.ds = "", nil
		ds, err := openDebugInfo(path, pdbPath, pdbForce)
		if err != nil {
			return err
		}
		debugCache.key, debugCache.ds = key, ds
	}
	return f(debugCache.ds)
}

// --- type_info operation ---

// errNoDebugInfo marks a binary without usable debug types; struct_layout
// then falls back to raw slots.
var errNoDebugInfo = errors.New("no debug types")

// openDebugInfo opens the debug information type_info reads: a PE's
// matching PDB, else its embedded DWARF (MinGW, Go); an ELF's DWARF.
func openDebugInfo(path, pdbPath string, pdbForce bool) (debugSource, error) {
	if f, err := pe.Open(path); err == nil {
		defer f.Close()
		_, is64 := f.OptionalHeader.(*pe.OptionalHeader64)
		note := ""
		if pdbPath != "none" {
			var pi *pdbInfo
			if pi, note = openPDBInfo(path, pdbPath, pdbForce, f, peImageBase(f), is64); pi != nil {
				return pi, nil
			}
		}
		if dd, err := f.DWARF(); err == nil {
			ps := int32(4)
			if is64 {
				ps = 8
			}
			return loadDWARFInfo("DWARF (embedded)", dd, ps), nil
		}
		if note == "" {
			note = "no PDB beside the image and no embedded DWARF"
		}
		if pdbPath == "none" {
			note = "pdb_path=none disables the PDB and the image has no embedded DWARF"
		}
		return nil, fmt.Errorf("%w: %s. Pass pdb_path to the image's PDB", errNoDebugInfo, note)
	}
	f, err := elf.Open(path)
	if err != nil {
		return nil, fmt.Errorf("%w: debug types come from a PE's PDB or DWARF, or an ELF's DWARF; %s is neither", errNoDebugInfo, path)
	}
	defer f.Close()
	dd, err := f.DWARF()
	if err != nil {
		return nil, fmt.Errorf("%w: no DWARF in %s (stripped?)", errNoDebugInfo, path)
	}
	ps := int32(4)
	if f.Class == elf.ELFCLASS64 {
		ps = 8
	}
	return loadDWARFInfo("DWARF", dd, ps), nil
}

// opTypeInfo prints the definitions of the named types: every member with
// its offset, every enumerator with its value.
func opTypeInfo(input AnalyzeInput) (string, error) {
	names := splitTargets(input.TypeName)
	if len(names) == 0 {
		return "", fmt.Errorf("type_name is required: a struct, class, union or enum name as decompile prints it (Node) or qualified (geo::Rect); separate up to %d with commas", typeInfoMaxNames)
	}
	if len(names) > typeInfoMaxNames {
		return "", fmt.Errorf("%d names requested, at most %d per call", len(names), typeInfoMaxNames)
	}
var sb strings.Builder
	err := withDebugInfo(input.FilePath, input.PDBPath, input.PDBForce, func(ds debugSource) error {
		typeInfoInto(&sb, ds, names)
		return nil
	})
	if err != nil {
		return "", err
	}
	return pageOutput(sb.String(), input.ResultOffset, input.MaxOutputChars, "type_info"), nil
}

func typeInfoInto(sb *strings.Builder, ds debugSource, names []string) {
	x := ds.typeIndex()
	fmt.Fprintf(sb, "Types from %s %s\n", ds.kind(), ds.file())
	for _, n := range names {
		sb.WriteString("\n")
		qs := x.find(n, true)
		switch {
		case len(qs) == 0:
			fmt.Fprintf(sb, "// %s: no struct/class/union/enum of that name", n)
			if sim := x.similar(n, 10); len(sim) > 0 {
				fmt.Fprintf(sb, "; similar: %s", strings.Join(sim, ", "))
			}
			sb.WriteString("\n")
			continue
		case len(qs) > typeInfoMaxMatches:
			fmt.Fprintf(sb, "// %s names %d types; pass a qualified one: %s, ...\n", n, len(qs), strings.Join(qs[:typeInfoMaxMatches], ", "))
			continue
		case len(qs) > 1:
			fmt.Fprintf(sb, "// %s names %d types: %s\n", n, len(qs), strings.Join(qs, ", "))
		}
		for _, q := range qs {
			ref := x.refs[q]
			d := ds.typeDesc(ref.ref)
			sb.WriteString(renderType(q, ref.alias, d, ds.overlapsOf(d), typeInfoMembers))
		}
	}
}

// pageOutput returns the window of out starting at offset (in characters),
// at most max long, with a note naming the result_offset that continues it.
func pageOutput(out string, offset, max int, op string) string {
	r := []rune(out)
	total := len(r)
	if offset > 0 {
		if offset >= total {
			return fmt.Sprintf("result_offset %d is past the end of the %s output (%d chars)\n", offset, op, total)
		}
		r = r[offset:]
	}
	if max > 0 && len(r) > max {
		return string(r[:max]) + fmt.Sprintf("\n... [chars %d-%d of %d shown; continue with result_offset=%d]\n", offset, offset+max, total, offset+max)
	}
	return string(r)
}
