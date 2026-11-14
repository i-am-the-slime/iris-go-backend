// Command codesize attributes the lines and closures of one generated Go file
// to their likely causes, so that work on code size starts from numbers.
//
//	compiler-backend/go/scripts/markgraf/code-size.sh GENERATED_DIR
//
// It reports the size of the file, then four views:
//
//   - duplicate top-level functions, hashed after renaming their locals
//     (exact), after erasing the names of referenced top-level functions and
//     values (callees: an upper bound for merging to a fixpoint), after
//     erasing type names (types), and after erasing both (shape); the
//     redundant lines of each level say how much merging modulo that
//     renaming could save;
//   - families: functions grouped by their name without its numeric
//     specialisation suffix, largest first;
//   - repeated statements and closures across the program (maximal ones
//     only), which is where inlining copies a body to many sites;
//   - closures by kind: wrappers whose body only forwards to a call, thunks,
//     and the rest.
package main

import (
	"bytes"
	"crypto/sha256"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"go/types"
	"os"
	"regexp"
	"sort"
	"strings"
)

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: codesize FILE.go")
		os.Exit(2)
	}
	source, err := os.ReadFile(os.Args[1])
	check(err)
	files := token.NewFileSet()
	file, err := parser.ParseFile(files, os.Args[1], source, parser.SkipObjectResolution)
	check(err)
	program := newProgram(files, file, source)
	program.reportTotals()
	program.reportDuplicates()
	program.reportFamilies()
	program.reportRepeats()
	program.reportClosures()
}

type program struct {
	files     *token.FileSet
	file      *ast.File
	source    []byte
	types     map[string]bool
	functions map[string]bool
	decls     []*ast.FuncDecl
	values    []*ast.ValueSpec
}

func newProgram(files *token.FileSet, file *ast.File, source []byte) *program {
	result := &program{files: files, file: file, source: source,
		types: map[string]bool{}, functions: map[string]bool{}}
	for _, declaration := range file.Decls {
		switch declaration := declaration.(type) {
		case *ast.FuncDecl:
			result.functions[declaration.Name.Name] = true
			result.decls = append(result.decls, declaration)
		case *ast.GenDecl:
			for _, spec := range declaration.Specs {
				switch spec := spec.(type) {
				case *ast.TypeSpec:
					result.types[spec.Name.Name] = true
				case *ast.ValueSpec:
					for _, name := range spec.Names {
						result.functions[name.Name] = true
					}
					if declaration.Tok == token.VAR && len(spec.Values) == 1 {
						result.values = append(result.values, spec)
					}
				}
			}
		}
	}
	return result
}

func (p *program) lines(node ast.Node) int {
	return p.files.Position(node.End()).Line - p.files.Position(node.Pos()).Line + 1
}

func (p *program) reportTotals() {
	literals := 0
	ast.Inspect(p.file, func(node ast.Node) bool {
		if _, ok := node.(*ast.FuncLit); ok {
			literals++
		}
		return true
	})
	fmt.Printf("== totals\n")
	fmt.Printf("bytes %d\nlines %d\ntop-level funcs %d\nfunc literals %d\ntypes %d\n\n",
		len(p.source), bytes.Count(p.source, []byte("\n")), len(p.decls), literals, len(p.types))
}

// Erasure says which names a normalised hash forgets.
type erasure struct {
	name                 string
	typeNames, topLevels bool
}

var (
	exact   = erasure{name: "exact"}
	callees = erasure{name: "callees", topLevels: true}
	typed   = erasure{name: "types", typeNames: true}
	shape   = erasure{name: "shape", typeNames: true, topLevels: true}
)

// normalised prints a node with its locals numbered in order of appearance and
// the names that the erasure forgets replaced by placeholders.
func (p *program) normalised(node ast.Node, erase erasure) string {
	locals := map[string]string{}
	var out strings.Builder
	var write func(node ast.Node)
	name := func(identifier string) {
		switch {
		case p.types[identifier]:
			if erase.typeNames {
				out.WriteString("T")
			} else {
				out.WriteString(identifier)
			}
		case p.functions[identifier]:
			if erase.topLevels {
				out.WriteString("F")
			} else {
				out.WriteString(identifier)
			}
		case types.Universe.Lookup(identifier) != nil:
			out.WriteString(identifier)
		default:
			renamed, ok := locals[identifier]
			if !ok {
				renamed = fmt.Sprintf("v%d", len(locals))
				locals[identifier] = renamed
			}
			out.WriteString(renamed)
		}
	}
	write = func(node ast.Node) {
		ast.Inspect(node, func(node ast.Node) bool {
			switch node := node.(type) {
			case nil:
				return false
			case *ast.Ident:
				name(node.Name)
				return false
			case *ast.SelectorExpr:
				write(node.X)
				out.WriteString("." + node.Sel.Name)
				return false
			case *ast.KeyValueExpr:
				if key, ok := node.Key.(*ast.Ident); ok {
					out.WriteString(key.Name + ":")
				} else {
					write(node.Key)
				}
				write(node.Value)
				return false
			case *ast.BasicLit:
				out.WriteString(node.Value)
			case *ast.BinaryExpr:
				out.WriteString(node.Op.String())
			case *ast.UnaryExpr:
				out.WriteString(node.Op.String())
			case *ast.AssignStmt:
				out.WriteString(node.Tok.String())
			case *ast.BranchStmt:
				out.WriteString(node.Tok.String())
			case *ast.IncDecStmt:
				out.WriteString(node.Tok.String())
			}
			fmt.Fprintf(&out, "(%T", node)
			defer out.WriteString(")")
			return true
		})
	}
	write(node)
	return out.String()
}

type named struct {
	name string
	node ast.Node
}

func hash(text string) [32]byte { return sha256.Sum256([]byte(text)) }

func (p *program) reportDuplicates() {
	fmt.Printf("== duplicate top-level functions (same body modulo renaming)\n")
	fmt.Printf("%-7s %8s %10s %10s\n", "level", "groups", "redundant", "red.lines")
	for _, erase := range []erasure{exact, callees, typed, shape} {
		groups := map[[32]byte][]named{}
		for _, declaration := range p.decls {
			body := &ast.FuncLit{Type: declaration.Type, Body: declaration.Body}
			key := hash("func" + p.normalised(body, erase))
			groups[key] = append(groups[key], named{declaration.Name.Name, declaration})
		}
		for _, value := range p.values {
			text := "var" + p.normalised(value.Values[0], erase)
			if value.Type != nil {
				text += p.normalised(value.Type, erase)
			}
			groups[hash(text)] = append(groups[hash(text)], named{value.Names[0].Name, value})
		}
		count, redundant, lines := 0, 0, 0
		type group struct {
			members []named
			lines   int
		}
		var listed []group
		for _, members := range groups {
			if len(members) < 2 {
				continue
			}
			count++
			redundant += len(members) - 1
			saved := (len(members) - 1) * p.lines(members[0].node)
			lines += saved
			listed = append(listed, group{members, saved})
		}
		fmt.Printf("%-7s %8d %10d %10d\n", erase.name, count, redundant, lines)
		sort.Slice(listed, func(i, j int) bool { return listed[i].lines > listed[j].lines })
		for index, group := range listed {
			if index == 8 {
				break
			}
			names := []string{}
			for i, member := range group.members {
				if i == 4 {
					names = append(names, "...")
					break
				}
				names = append(names, member.name)
			}
			fmt.Printf("    %6d lines  %3d x %4d  %s\n", group.lines, len(group.members),
				p.lines(group.members[0].node), strings.Join(names, " "))
		}
	}
	fmt.Println()
}

var specialisationSuffix = regexp.MustCompile(`[0-9]+$`)

func (p *program) reportFamilies() {
	type family struct {
		name         string
		count, lines int
	}
	families := map[string]*family{}
	for _, declaration := range p.decls {
		base := specialisationSuffix.ReplaceAllString(declaration.Name.Name, "")
		if families[base] == nil {
			families[base] = &family{name: base}
		}
		families[base].count++
		families[base].lines += p.lines(declaration)
	}
	var listed []*family
	for _, family := range families {
		listed = append(listed, family)
	}
	sort.Slice(listed, func(i, j int) bool { return listed[i].lines > listed[j].lines })
	fmt.Printf("== families (name without numeric suffix), by lines\n")
	for _, family := range listed[:min(30, len(listed))] {
		fmt.Printf("%7d lines %5d funcs  %s\n", family.lines, family.count, family.name)
	}
	fmt.Println()
}

// reportRepeats finds statements and closures that occur more than once in the
// program, after renaming locals, and counts only the outermost repeats.
func (p *program) reportRepeats() {
	type occurrence struct {
		node      ast.Node
		enclosing string
	}
	groups := map[[32]byte][]occurrence{}
	for _, declaration := range p.decls {
		ast.Inspect(declaration.Body, func(node ast.Node) bool {
			switch node.(type) {
			case ast.Stmt, *ast.FuncLit:
			default:
				return true
			}
			if _, ok := node.(*ast.BlockStmt); ok || node == nil || p.lines(node) < 4 {
				return true
			}
			key := hash(p.normalised(node, exact))
			groups[key] = append(groups[key], occurrence{node, declaration.Name.Name})
			return true
		})
	}
	type repeat struct {
		occurrences []occurrence
		saved       int
	}
	var repeats []repeat
	for _, occurrences := range groups {
		if len(occurrences) > 1 {
			saved := (len(occurrences) - 1) * p.lines(occurrences[0].node)
			repeats = append(repeats, repeat{occurrences, saved})
		}
	}
	sort.Slice(repeats, func(i, j int) bool { return repeats[i].saved > repeats[j].saved })
	covered := map[token.Pos]token.Pos{}
	overlaps := func(node ast.Node) bool {
		for start, end := range covered {
			if node.Pos() < end && start < node.End() {
				return true
			}
		}
		return false
	}
	total := 0
	var maximal []repeat
	for _, repeat := range repeats {
		if overlaps(repeat.occurrences[0].node) {
			continue
		}
		for _, occurrence := range repeat.occurrences {
			covered[occurrence.node.Pos()] = occurrence.node.End()
		}
		total += repeat.saved
		maximal = append(maximal, repeat)
	}
	fmt.Printf("== repeated statements/closures (>= 4 lines, outermost), redundant lines %d\n", total)
	for _, repeat := range maximal[:min(60, len(maximal))] {
		first := repeat.occurrences[0]
		enclosing := map[string]bool{}
		for _, occurrence := range repeat.occurrences {
			enclosing[occurrence.enclosing] = true
		}
		var buffer bytes.Buffer
		check(printer.Fprint(&buffer, p.files, first.node))
		headline := strings.SplitN(buffer.String(), "\n", 2)[0]
		fmt.Printf("%7d lines %4d x %4d in %3d funcs (e.g. %s)  %.90s\n", repeat.saved,
			len(repeat.occurrences), p.lines(first.node), len(enclosing), first.enclosing, headline)
	}
	fmt.Println()
}

func (p *program) reportClosures() {
	kinds := map[string][2]int{}
	ast.Inspect(p.file, func(node ast.Node) bool {
		literal, ok := node.(*ast.FuncLit)
		if !ok {
			return true
		}
		kind := "other"
		switch {
		case len(literal.Type.Params.List) == 0:
			kind = "thunk (no parameters)"
		case forwards(literal):
			kind = "wrapper (body is one forwarding call)"
		}
		counts := kinds[kind]
		kinds[kind] = [2]int{counts[0] + 1, counts[1] + p.lines(literal)}
		return true
	})
	fmt.Printf("== closures by kind (lines include nested closures)\n")
	names := make([]string, 0, len(kinds))
	for kind := range kinds {
		names = append(names, kind)
	}
	sort.Strings(names)
	for _, kind := range names {
		fmt.Printf("%7d closures %8d lines  %s\n", kinds[kind][0], kinds[kind][1], kind)
	}
}

// forwards says whether a closure only returns, or evaluates, a single call
// whose arguments are its parameters or names in scope.
func forwards(literal *ast.FuncLit) bool {
	if len(literal.Body.List) != 1 {
		return false
	}
	var call ast.Expr
	switch statement := literal.Body.List[0].(type) {
	case *ast.ReturnStmt:
		if len(statement.Results) != 1 {
			return false
		}
		call = statement.Results[0]
	case *ast.ExprStmt:
		call = statement.X
	default:
		return false
	}
	expression, ok := call.(*ast.CallExpr)
	if !ok {
		return false
	}
	for _, argument := range expression.Args {
		switch argument.(type) {
		case *ast.Ident, *ast.SelectorExpr, *ast.BasicLit:
		default:
			return false
		}
	}
	return true
}

func check(err error) {
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
