package analyze

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"github.com/knewstimek/gosleigh/pkg/pcode"
	"github.com/modelcontextprotocol/go-sdk/mcp"
)

// The types a decompiled function names follow it, with member offsets and
// enum values: without them an agent sees Node, Color and a masked constant
// it has no way to decode.
func TestDecompileTypeSection(t *testing.T) {
	out := decompileFixture(t, "x64", "use_node")
	for _, want := range []string{
		"// types named above",
		"struct Node { // 0x48 bytes",
		"+0x24 Flags flags;",
		"enum Color { Red = 1, Green = 2, Blue = 0x9c40 (40000) };",
		// The compiler's & 0xfffffffb | 0xa store (gosleigh's maskedConstant).
		"(n->flags).mode = 5;",
	} {
		if !strings.Contains(out, want) {
			t.Errorf("output lacks %q:\n%s", want, out)
		}
	}
	// Point is reachable from Node but not named in the C: left to type_info.
	if strings.Contains(out, "struct Point {") {
		t.Errorf("type section prints an unnamed type:\n%s", out)
	}
}

func TestTypeInfo(t *testing.T) {
	exe := filepath.Join("testdata", "pdb", "fixture_x64.exe")
	out, err := opTypeInfo(AnalyzeInput{FilePath: exe, TypeName: "Rect, color, Colr, Pointt", MaxOutputChars: 100000})
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"struct Rect { // geo::Rect, 0x18 bytes", // short name, namespace in the comment
		"+0x00 Shape super_Shape; // base class",
		"enum Color {", // case-insensitive
		"// Colr: no struct/class/union/enum of that name; similar: Color",
		"similar: Point",
	} {
		if !strings.Contains(out, want) {
			t.Errorf("type_info lacks %q:\n%s", want, out)
		}
	}
	if _, err := opTypeInfo(AnalyzeInput{FilePath: exe}); err == nil {
		t.Error("type_info without type_name: want an error")
	}
}

func TestDecompileNameResolution(t *testing.T) {
	out := decompileFixture(t, "x64", "Rect::area, area, use_nod, node")
	if n := strings.Count(out, "// geo::Rect::area @"); n != 2 {
		t.Errorf("suffix names resolved %d times, want 2:\n%s", n, out)
	}
	if !strings.Contains(out, `"use_nod" is neither`) || !strings.Contains(out, "similar: use_node @ 0x") {
		t.Errorf("typo without a suggestion:\n%s", out)
	}
	if !strings.Contains(out, `"node" is neither`) || strings.Contains(out, "function_at va=node") {
		t.Errorf("name error suggests function_at on a name:\n%s", out)
	}
}

func TestLookupNameAmbiguous(t *testing.T) {
	h := &decompHost{funcs: map[uint64]string{0x10: "a::Draw", 0x20: "b::Draw", 0x30: "Draw2"}}
	h.finish()
	if m, _ := h.lookupName("Draw"); !reflect.DeepEqual(m, []uint64{0x10, 0x20}) {
		t.Errorf("Draw = %x, want both overloads", m)
	}
	if m, _ := h.lookupName("b::Draw"); !reflect.DeepEqual(m, []uint64{0x20}) {
		t.Errorf("b::Draw = %x", m)
	}
}

func TestDecompilePaging(t *testing.T) {
	exe := filepath.Join("testdata", "pdb", "fixture_x64.exe")
	full, _ := opDecompile(context.Background(), AnalyzeInput{FilePath: exe, VA: "use_node", MaxOutputChars: 100000})
	var got strings.Builder
	for off := 0; off < 100000; off += 400 {
		page, _ := opDecompile(context.Background(), AnalyzeInput{FilePath: exe, VA: "use_node", MaxOutputChars: 400, ResultOffset: off})
		body, _, cut := strings.Cut(page, "\n... [chars ")
		got.WriteString(body)
		if !cut {
			break
		}
		if !strings.Contains(page, "result_offset=") {
			t.Fatalf("truncated page without a continuation:\n%s", page)
		}
	}
	// Timings differ between runs; compare the C.
	strip := func(s string) string { return s[strings.Index(s, "int use_node"):] }
	if strip(got.String()) != strip(full) {
		t.Errorf("pages do not add up to the output:\n%s\n---\n%s", got.String(), full)
	}
}

// C's typedef'd tagless structures and enums (gcc DWARF in a MinGW PE):
// printed by the typedef name instead of an anon_N counter, listed with
// the function, found by type_info and by field xref.
func TestDWARFTypedefTypes(t *testing.T) {
	gcc, err := exec.LookPath("gcc")
	if err != nil {
		t.Skip("gcc not found")
	}
	dir := t.TempDir()
	src := filepath.Join(dir, "td.c")
	code := "typedef enum { MODE_OFF, MODE_ON = 16, MODE_AUTO = 32 } Mode;\n" +
		"typedef struct { int hp; Mode mode; int level; } Obj;\n" +
		"__attribute__((noinline)) int check(Obj *o) { if (o->mode == MODE_AUTO) return o->level; return o->hp; }\n" +
		"int main(void) { Obj o = {0}; return check(&o); }\n"
	if err := os.WriteFile(src, []byte(code), 0o644); err != nil {
		t.Fatal(err)
	}
	bin := filepath.Join(dir, "td.exe")
	if out, err := exec.Command(gcc, "-g", "-O2", "-o", bin, src).CombinedOutput(); err != nil {
		t.Skipf("gcc cannot build here: %v\n%s", err, out)
	}
	out, err := opDecompile(context.Background(), AnalyzeInput{FilePath: bin, VA: "check", MaxOutputChars: 100000})
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"check(Obj *o)", "struct Obj {", "+0x04 Mode mode;", "MODE_ON = 0x10 (16)"} {
		if !strings.Contains(out, want) {
			t.Errorf("decompile lacks %q:\n%s", want, out)
		}
	}
	if strings.Contains(out, "anon_") {
		t.Errorf("tagless type printed by a counter name:\n%s", out)
	}
	ti, err := opTypeInfo(AnalyzeInput{FilePath: bin, TypeName: "Obj, Mode", MaxOutputChars: 100000})
	if err != nil || !strings.Contains(ti, "+0x08 int level;") || !strings.Contains(ti, "MODE_AUTO = 0x20 (32)") {
		t.Errorf("type_info: %v\n%s", err, ti)
	}
	xr, err := opXref(context.Background(), AnalyzeInput{FilePath: bin, Field: "Obj::mode"})
	if err != nil || !strings.Contains(xr, "check @") {
		t.Errorf("field xref on a typedef'd struct: %v\n%s", err, xr)
	}
}

// struct_layout on a typed global shows its members with values instead
// of pointer-sized slots; type_name lays a type over any address.
func TestStructLayoutTyped(t *testing.T) {
	exe := filepath.Join("testdata", "pdb", "fixture_x64.exe")
	ds, err := openDebugInfo(exe, "", false)
	if err != nil {
		t.Fatal(err)
	}
	var globals []pdbData
	for _, g := range ds.(*pdbInfo).data {
		globals = append(globals, g)
	}
	if len(globals) == 0 {
		t.Skip("fixture has no globals")
	}
	for _, g := range globals {
		out, err := opStructLayout(AnalyzeInput{FilePath: exe, VA: fmt.Sprintf("0x%x", g.va)})
		if err != nil {
			t.Fatalf("%s: %v", g.name, err)
		}
		t.Logf("%s", out)
		if !strings.Contains(out, "Typed layout: "+g.name) {
			t.Errorf("%s: not typed:\n%s", g.name, out)
		}
	}
	out, err := opStructLayout(AnalyzeInput{FilePath: exe, VA: fmt.Sprintf("0x%x", globals[0].va), TypeName: "Point"})
	if err != nil || !strings.Contains(out, "Point laid over") || !strings.Contains(out, "+0x0004 int y = ") {
		t.Errorf("type_name over a global: %v\n%s", err, out)
	}
	if _, err := opStructLayout(AnalyzeInput{FilePath: exe, VA: fmt.Sprintf("0x%x", globals[0].va), TypeName: "Pointt"}); err == nil || !strings.Contains(err.Error(), "similar: Point") {
		t.Errorf("unknown type_name: %v", err)
	}
}

// Address operations take the symbol names decompile and disassembly print.
func TestSymbolNameVA(t *testing.T) {
	exe, _ := filepath.Abs(filepath.Join("testdata", "pdb", "fixture_x64.exe"))
	call := func(in AnalyzeInput) (string, bool) {
		in.FilePath = exe
		res, _, _ := Handle(context.Background(), nil, in)
		return res.Content[0].(*mcp.TextContent).Text, res.IsError
	}
	for _, c := range []struct {
		in   AnalyzeInput
		want string
	}{
		{AnalyzeInput{Operation: "disassemble", VA: "use_node", Count: 2}, "0x140001074:"},
		{AnalyzeInput{Operation: "disassemble", VA: "use_node+0x9", Count: 1}, "0x14000107d:"},
		{AnalyzeInput{Operation: "function_at", VA: "Rect::area"}, "Name:   geo::Rect::area"},
		{AnalyzeInput{Operation: "xref", TargetVA: "g_rect"}, "references to 0x140003018"},
		{AnalyzeInput{Operation: "struct_layout", VA: "g_handle"}, "uint g_handle = 7"},
	} {
		if out, isErr := call(c.in); isErr || !strings.Contains(out, c.want) {
			t.Errorf("%s %s%s: lacks %q:\n%s", c.in.Operation, c.in.VA, c.in.TargetVA, c.want, out)
		}
	}
	if out, isErr := call(AnalyzeInput{Operation: "hexdump", VA: "use_nod"}); !isErr || !strings.Contains(out, "similar: use_node @ 0x140001074") {
		t.Errorf("typo: %s", out)
	}
}

func TestTypeTokens(t *testing.T) {
	c := `int f(Node *n, TArray<FString,0> *a, main.Point p) {
    /* WARNING: Color */
    s = "Flags";
    n->Rect = g(x.Value);
    return (Shape)n;
}`
	got := typeTokens(c)
	want := []string{"int", "Node", "n", "TArray<FString,0>", "TArray", "FString", "a", "main.Point", "main", "p", "s", "x.Value", "x", "Shape"}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("typeTokens =\n %q\nwant\n %q", got, want)
	}
}

// A structure larger than the section's member cap shows the members the
// function uses, not its first ones.
func TestRenderTypeNarrowsToUsed(t *testing.T) {
	intT := &pcode.HostTypeDesc{Name: "int", Meta: "int", Size: 4}
	d := &pcode.HostTypeDesc{Name: "Big", Meta: "struct", Size: 400}
	for i := 0; i < 100; i++ {
		d.Fields = append(d.Fields, pcode.HostFieldDesc{Name: fmt.Sprintf("m%d", i), Offset: int32(4 * i), Type: intT})
	}
	out := renderType("Big", false, d, nil, 32, map[string]bool{"m77": true})
	if !strings.Contains(out, "+0x134 int m77;") || strings.Contains(out, "m0;") || !strings.Contains(out, "1 of 100 members") {
		t.Errorf("narrowed render:\n%s", out)
	}
	if out := renderType("Big", false, d, nil, 32, nil); !strings.Contains(out, "m0;") || !strings.Contains(out, "68 more members") {
		t.Errorf("type_info render:\n%s", out)
	}
}

func TestNearName(t *testing.T) {
	for _, c := range []struct {
		a, b string
		want bool
	}{{"color", "colr", true}, {"takedamage", "takedamge", true}, {"point", "pointt", true}, {"rect", "node", false}, {"ab", "xy", false}} {
		if got := nearName(c.a, c.b); got != c.want {
			t.Errorf("nearName(%q, %q) = %v", c.a, c.b, got)
		}
	}
}
