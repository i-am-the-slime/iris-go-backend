package Dhall_Parser_ffi

import (
	"math"
	"math/big"
	"slices"
	"strconv"
	"strings"
	"unicode/utf16"
	"unicode/utf8"

	"github.com/i-am-the-slime/iris-go/prim"
)

// The grammar's postprocessors (the JavaScript between {% and %} in dhall/grammar.ne), ported one
// by one. They build JavaScript values, which here are nil for null, string, float64 for a
// number, int32 for a number Dhall.Parser reads as an Int, []any for an array and *node for an
// object. Arrays are never changed in place, since several parses share them; the one object a
// postprocessor changes, an http import, is shared by pointer, as in JavaScript.

// A node is the object `{ type, value }` a postprocessor builds for an expression or an import.
type node struct {
	kind  string
	value []any
}

// rejection is nearley's Parser.fail, which a postprocessor returns to reject a parse.
type rejection struct{}

var reject any = rejection{}

var keywords = []string{
	"if", "then", "else", "let", "in", "using", "missing", "as", "Infinity", "NaN", "merge", "Some",
	"toMap", "assert", "forall", "with",
}

var builtins = []string{
	"Type", "Kind", "Sort", "Bool", "True", "False", "missing", "Natural", "Natural/fold",
	"Natural/build", "Natural/isZero", "Natural/even", "Natural/odd", "Natural/toInteger",
	"Natural/show", "Natural/subtract", "Integer", "Integer/show", "Integer/toDouble",
	"Integer/negate", "Integer/clamp", "Double", "Double/show", "Text", "Text/show", "Text/replace",
	"List", "List/build", "List/fold", "List/length", "List/head", "List/last", "List/indexed",
	"List/reverse", "Date", "Time", "TimeZone", "Optional", "None",
}

type postprocessor = func(d []any) any

// nearley's own postprocessors and the grammar's helpers.

func id(d []any) any { return d[0] }

func joiner(d []any) any { return join(d, "") }

func arrpush(d []any) any { return concat(d[0].([]any), []any{d[1]}) }

func nuller([]any) any { return nil }

func collapse(d []any) any { return collapsed(d) }

func pass(n int) postprocessor { return func(d []any) any { return passOf(n, d) } }

// passOf is the grammar's `pass(n)(value)`: `value ? value[n] : null`.
func passOf(n int, value any) any {
	if !truthy(value) {
		return nil
	}
	return element(value, n)
}

func tag(kind string) postprocessor { return func(d []any) any { return &node{kind, d} } }

// binop folds the repetitions of an operator to the left: `binop(type, i, flatten)`.
func binop(kind string, i int, flatten bool) postprocessor {
	return func(d []any) any {
		result := d[0]
		for _, repetition := range d[1].([]any) {
			operand := element(repetition, i)
			if flatten {
				result = &node{kind, concat([]any{result}, operand)}
			} else {
				result = &node{kind, []any{result, operand}}
			}
		}
		return result
	}
}

func constant(value any) postprocessor { return func([]any) any { return value } }

// array is a postprocessor that builds a new array of the values each time, like an array literal.
func array(values ...any) postprocessor {
	return func([]any) any { return slices.Clone(values) }
}

func emptyNode(kind string) postprocessor {
	return func([]any) any { return &node{kind, []any{}} }
}

// absent stands for a `null` among the fields of a node.
const absent = -1

// fields builds `{ type: kind, value: [d[i], ...] }`.
func fields(kind string, indices ...int) postprocessor {
	return func(d []any) any {
		value := make([]any, len(indices))
		for position, index := range indices {
			if index != absent {
				value[position] = d[index]
			}
		}
		return &node{kind, value}
	}
}

// wrap builds `{ type: kind, value: d[0] }`.
func wrap(kind string) postprocessor {
	return func(d []any) any { return &node{kind, d[0].([]any)} }
}

// picks builds `[d[i], ...]`.
func picks(indices ...int) postprocessor {
	return func(d []any) any {
		value := make([]any, len(indices))
		for position, index := range indices {
			value[position] = d[index]
		}
		return value
	}
}

// The grammar's inline postprocessors, named after what they build.

func simpleLabel(d []any) any {
	label := d[0].(string) + join(d[1].([]any), "")
	if slices.Contains(keywords, label) {
		return reject
	}
	return label
}

func nonreservedLabel(d []any) any {
	if slices.Contains(builtins, d[0].(string)) {
		return reject
	}
	return d[0]
}

func finiteDouble(d []any) any {
	value := d[0].(float64)
	if math.IsInf(value, 0) || math.IsNaN(value) {
		return reject
	}
	return value
}

func arrowType(d []any) any { return &node{"Pi", []any{"_", d[0], d[4]}} }

func environmentImport(d []any) any {
	variable := d[1].([]any)
	if len(variable) == 1 {
		return &node{"Env", []any{variable[0]}}
	}
	return &node{"Env", []any{variable[1]}}
}

func emptyList(d []any) any { return &node{"ListLit", []any{[]any{}, d[7]}} }

func nonEmptyList(d []any) any {
	elements := concat([]any{d[3]}, mapped(d[5], 2))
	return &node{"ListLit", []any{elements, nil}}
}

// localImport builds a local import of the path at d[index]: its directory and its file.
func localImport(prefix string, index int) postprocessor {
	return func(d []any) any {
		path := d[index].([]any)
		directory := slices.Clone(path[:len(path)-1])
		return &node{"Local", []any{prefix, directory, path[len(path)-1]}}
	}
}

func recordType(d []any) any { return &node{"Record", concat([]any{d[0]}, mapped(d[1], 3))} }

func recordLiteral(d []any) any {
	return &node{"RecordLit", mergeFields(concat([]any{d[0]}, mapped(d[1], 3)))}
}

func dateTimeZoneLiteral(d []any) any {
	return &node{"RecordLit", []any{
		[]any{"date", &node{"DateLit", d[0].([]any)}},
		[]any{"time", &node{"TimeLit", d[2].([]any)}},
		[]any{"timeZone", &node{"TimeZoneLit", d[3].([]any)}},
	}}
}

func dateTimeLiteral(d []any) any {
	return &node{"RecordLit", []any{
		[]any{"date", &node{"DateLit", d[0].([]any)}},
		[]any{"time", &node{"TimeLit", d[2].([]any)}},
	}}
}

func timeZoneTimeLiteral(d []any) any {
	return &node{"RecordLit", []any{
		[]any{"time", &node{"TimeLit", d[0].([]any)}},
		[]any{"timeZone", &node{"TimeZoneLit", d[1].([]any)}},
	}}
}

// remoteImport builds `[scheme, authority, directory, file, query]`; httpImport adds the headers.
func remoteImport(d []any) any {
	path := d[3].([]any)
	directory := []any{}
	var file any = ""
	if len(path) > 0 {
		directory = slices.Clone(path[:len(path)-1])
		if last := path[len(path)-1]; truthy(last) {
			file = last
		}
	}
	return &node{"Remote", []any{d[0], d[2], directory, file, passOf(1, d[4])}}
}

// httpImport sets the headers of the remote import that d[0] shares with every other parse of it:
// `d[0].value[5] = pass(3)(d[1])`.
func httpImport(d []any) any {
	remote := d[0].(*node)
	headers := passOf(3, d[1])
	if len(remote.value) == 5 {
		remote.value = append(remote.value, headers)
	} else {
		remote.value[5] = headers
	}
	return remote
}

func unionType(d []any) any { return &node{"Union", concat([]any{d[0]}, d[1])} }

// variable is `{ type: "Var", value: [d[0], (pass(2)(d[1]) || 0) | 0] }`.
func variable(d []any) any {
	index := passOf(2, d[1])
	if !truthy(index) {
		return &node{"Var", []any{d[0], int32(0)}}
	}
	return &node{"Var", []any{d[0], toInt32(stringToNumber(index.(string)))}}
}

func builtinIdentifier(d []any) any { return &node{d[0].(string), []any{}} }

func withClause(d []any) any { return []any{concat([]any{d[0]}, mapped(d[1], 3)), d[5]} }

func punnedEntry(d []any) any { return []any{d[0], &node{"Var", []any{d[0], int32(0)}}} }

// partialTime is `[d[0], d[2], d[4] + (d[5] ? d[5][0] : "")]`: the fraction's first code unit
// only, its point, since d[5] is the fraction itself.
func partialTime(d []any) any {
	seconds := d[4].(string)
	if truthy(d[5]) {
		seconds += toString(element(d[5], 0))
	}
	return []any{d[0], d[2], seconds}
}

func timeNumoffset(d []any) any { return []any{element(d[0], 0), d[1], d[3]} }

// dottedEntry nests `a.b.c = e` into `a = { b = { c = e } }`.
func dottedEntry(d []any) any {
	labels := d[1].([]any)
	value := d[5]
	for i := len(labels) - 1; i >= 0; i-- {
		value = &node{"RecordLit", []any{[]any{element(labels[i], 3), value}}}
	}
	return []any{d[0], value}
}

func unionEntry(d []any) any { return []any{d[0], passOf(3, d[1])} }

func prepend(d []any) any { return concat([]any{d[0]}, d[1]) }

func letBinding(d []any) any { return []any{d[2], passOf(2, d[4]), d[7]} }

// doubleQuoteChunk is a literal chunk followed by interpolations and literal chunks, the last
// one extended by a trailing "$".
func doubleQuoteChunk(d []any) any {
	chunks := concat([]any{d[0]}, d[1].([]any)...)
	if d[2] != nil {
		last := len(chunks) - 1
		chunks[last] = toString(chunks[last]) + toString(d[2])
	}
	return chunks
}

func numericDouble(d []any) any { return stringToNumber(join(flattened(d), "")) }

func hashDigest(d []any) any { return collapsed(d[1:]) }

func joinFirst(d []any) any { return join(d[0].([]any), "") }

// letExpression nests the bindings of `let a = x let b = y in e` to the right.
func letExpression(d []any) any {
	bindings := d[0].([]any)
	body := d[3]
	for i := len(bindings) - 1; i >= 0; i-- {
		body = &node{"Let", concat(bindings[i].([]any), body)}
	}
	return body
}

func firstOfFirst(d []any) any { return element(d[0], 0) }

func completion(d []any) any {
	if d[1] == nil {
		return d[0]
	}
	return &node{"RecordCompletion", []any{d[0], element(d[1], 3)}}
}

func hashed(d []any) any {
	if d[1] == nil {
		return d[0]
	}
	return &node{"Hashed", []any{d[0], element(d[1], 1)}}
}

func annotated(d []any) any {
	if d[1] == nil {
		return d[0]
	}
	return &node{"Annot", []any{d[0], element(d[1], 3)}}
}

// selectors folds `e.a.{ b }.(t)` to the left, each selector a Field, Project or ProjectType.
func selectors(d []any) any {
	result := d[0]
	for _, selection := range d[1].([]any) {
		selector := element(selection, 3).(*node)
		result = &node{selector.kind, []any{result, selector.value[0]}}
	}
	return result
}

func labels(d []any) any {
	if d[3] == nil {
		return []any{}
	}
	return concat([]any{element(d[3], 0)}, mapped(element(d[3], 2), 2))
}

func singleQuoteLiteral(d []any) any { return removeCommonPrefix(d[2].([]any)) }

// unbracedEscape is `String.fromCharCode(parseInt(d[0], 16))`.
func unbracedEscape(d []any) any { return codeUnitString(uint16(hexadecimal(d[0]))) }

// bracedEscape is `String.fromCodePoint(parseInt(d[1], 16))`.
func bracedEscape(d []any) any { return string(rune(hexadecimal(d[1]))) }

// mergeFields combines the repeated fields of a record literal, `{ a = x, a = y }`, into
// `{ a = x ∧ y }`, at the position of the first.
func mergeFields(entries []any) []any {
	result := []any{}
	for _, entry := range entries {
		field, value := element(entry, 0), element(entry, 1)
		found := false
		for i, merged := range result {
			if key, existing := element(merged, 0), element(merged, 1); key == field {
				found = true
				result[i] = []any{key, &node{"Combine", []any{existing, value}}}
			}
		}
		if !found {
			result = append(result, []any{field, value})
		}
	}
	return result
}

// removeCommonPrefix strips the indentation that every line of a multi-line literal shares. The
// items are strings and interpolated expressions; the result has a string per code point.
func removeCommonPrefix(items []any) []any {
	iterate := func(visit func(character any)) {
		for _, item := range items {
			text, ok := item.(string)
			if !ok {
				visit(item)
				continue
			}
			for _, character := range text {
				visit(string(character))
			}
		}
	}
	var prefixes []string
	prefix, scanning := "", true
	gatherPrefixes := func(character any) {
		switch {
		case character == "\n":
			prefix, scanning = "", true
		case !scanning:
		case character == "\t" || character == " ":
			prefix += character.(string)
		default:
			prefixes = append(prefixes, prefix)
			scanning = false
		}
	}
	iterate(gatherPrefixes)
	gatherPrefixes(nil)
	common := prefixes[0]
	for _, other := range prefixes[1:] {
		common = commonPrefix(common, other)
	}
	result := []any{}
	removal := common
	iterate(func(character any) {
		keep := true
		if character == "\n" {
			removal = common
		} else if removal != "" {
			if character == removal[:1] {
				keep = false
				removal = removal[1:]
			} else {
				removal = ""
			}
		}
		if keep {
			result = append(result, character)
		}
	})
	return result
}

func commonPrefix(a, b string) string {
	length := 0
	for length < len(a) && length < len(b) && a[length] == b[length] {
		length++
	}
	return a[:length]
}

// JavaScript's operations on the values.

// concat is Array.prototype.concat: an array argument contributes its elements.
func concat(base []any, values ...any) []any {
	result := slices.Clone(base)
	for _, value := range values {
		if elements, ok := value.([]any); ok {
			result = append(result, elements...)
		} else {
			result = append(result, value)
		}
	}
	return result
}

// mapped is `array.map(v => v[index])`.
func mapped(values any, index int) []any {
	elements := values.([]any)
	result := make([]any, len(elements))
	for i, value := range elements {
		result[i] = element(value, index)
	}
	return result
}

// element is `value[index]`, of an array or of a string's code units; nil where it is undefined.
func element(value any, index int) any {
	switch value := value.(type) {
	case []any:
		if index < len(value) {
			return value[index]
		}
	case string:
		if units := utf16.Encode([]rune(value)); index < len(units) {
			return codeUnitString(units[index])
		}
	}
	return nil
}

func truthy(value any) bool {
	switch value := value.(type) {
	case nil:
		return false
	case string:
		return value != ""
	case float64:
		return value != 0 && !math.IsNaN(value)
	case int32:
		return value != 0
	}
	return true
}

// toString is JavaScript's String(value).
func toString(value any) string {
	switch value := value.(type) {
	case nil:
		return "null"
	case string:
		return value
	case float64:
		return prim.NumberToString(value)
	case int32:
		return strconv.Itoa(int(value))
	case []any:
		return join(value, ",")
	}
	return "[object Object]"
}

// join is Array.prototype.join, which writes null as nothing.
func join(values []any, separator string) string {
	texts := make([]string, len(values))
	for i, value := range values {
		if value != nil {
			texts[i] = toString(value)
		}
	}
	return strings.Join(texts, separator)
}

// flattened is the grammar's `flatten`: the leaves of nested arrays.
func flattened(values []any) []any {
	var leaves []any
	for _, value := range values {
		if elements, ok := value.([]any); ok {
			leaves = append(leaves, flattened(elements)...)
		} else {
			leaves = append(leaves, value)
		}
	}
	return leaves
}

// collapsed is the grammar's `collapse`: the strings of nested arrays, concatenated.
func collapsed(values []any) string {
	var text strings.Builder
	for _, value := range values {
		if elements, ok := value.([]any); ok {
			text.WriteString(collapsed(elements))
		} else if value != nil {
			text.WriteString(toString(value))
		}
	}
	return pairSurrogates(text.String())
}

// stringToNumber is JavaScript's Number(text) for the numerals the grammar accepts: decimal,
// with an optional sign, fraction and exponent, or hexadecimal with a 0x prefix.
func stringToNumber(text string) float64 {
	if digits, ok := strings.CutPrefix(text, "0x"); ok {
		integer, _ := new(big.Int).SetString(digits, 16)
		value, _ := new(big.Float).SetInt(integer).Float64()
		return value
	}
	value, _ := strconv.ParseFloat(text, 64)
	return value
}

// toInt32 is JavaScript's `value | 0`.
func toInt32(value float64) int32 {
	if math.IsInf(value, 0) || math.IsNaN(value) {
		return 0
	}
	return int32(uint32(int64(math.Mod(math.Trunc(value), 1<<32))))
}

// hexadecimal is `parseInt(text, 16)` of the hexadecimal digits of a Unicode escape.
func hexadecimal(text any) int {
	value := 0
	for _, digit := range text.(string) {
		value = value*16 + hexadecimalDigit(digit)
	}
	return value
}

func hexadecimalDigit(digit rune) int {
	switch {
	case digit >= 'a':
		return int(digit-'a') + 10
	case digit >= 'A':
		return int(digit-'A') + 10
	}
	return int(digit - '0')
}

// Strings are Go strings, but a token is one UTF-16 code unit. A surrogate on its own is written
// as the three bytes UTF-8 would give its code point, and pairSurrogates joins a high and a low
// surrogate that end up next to each other into the character they encode. The grammar only
// accepts surrogates in pairs, which valid_non_ascii collapses at once.

func codeUnitString(unit uint16) string {
	if !utf16.IsSurrogate(rune(unit)) {
		return string(rune(unit))
	}
	return string([]byte{0xED, byte(0x80 | unit>>6&0x3F), byte(0x80 | unit&0x3F)})
}

func pairSurrogates(text string) string {
	if !strings.Contains(text, "\xED") {
		return text
	}
	var paired strings.Builder
	for i := 0; i < len(text); {
		high, isHigh := surrogateAt(text, i)
		low, isLow := surrogateAt(text, i+3)
		if isHigh && isLow && high < 0xDC00 && low >= 0xDC00 {
			paired.WriteRune(utf16.DecodeRune(high, low))
			i += 6
			continue
		}
		_, size := utf8.DecodeRuneInString(text[i:])
		paired.WriteString(text[i : i+size])
		i += size
	}
	return paired.String()
}

func surrogateAt(text string, i int) (rune, bool) {
	if i+3 > len(text) || text[i] != 0xED || text[i+1] < 0xA0 {
		return 0, false
	}
	return 0xD000 | rune(text[i+1]&0x3F)<<6 | rune(text[i+2]&0x3F), true
}
