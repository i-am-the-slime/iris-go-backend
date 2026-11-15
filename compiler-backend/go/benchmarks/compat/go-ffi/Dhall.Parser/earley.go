package Dhall_Parser_ffi

import "unicode/utf16"

// This file is nearley's Earley parser (lib/nearley.js in nearley 2.20.1), ported statement for
// statement: the order in which it creates, completes and predicts states decides the order of
// the parses it reports, and so which of several ambiguous parses Dhall.Parser picks. The lexer is
// nearley's StreamLexer, whose tokens are the UTF-16 code units of the input.

// A rule is one alternative of a nonterminal. A postprocessor builds the rule's value from the
// values of its symbols; without one the value is the array of those values.
type rule struct {
	name        int
	symbols     []symbol
	postprocess postprocessor
}

// A symbol is a nonterminal, or a terminal that accepts the code units in its ranges.
type symbol struct {
	expects int
	ranges  []uint16
}

const terminal = -1

func nonterminal(name int) symbol { return symbol{expects: name} }

func literal(unit uint16) symbol { return symbol{expects: terminal, ranges: []uint16{unit, unit}} }

// units is a terminal of inclusive lower and upper bounds, in pairs.
func units(bounds ...uint16) symbol { return symbol{expects: terminal, ranges: bounds} }

func (s symbol) accepts(unit uint16) bool {
	for i := 0; i < len(s.ranges); i += 2 {
		if s.ranges[i] <= unit && unit <= s.ranges[i+1] {
			return true
		}
	}
	return false
}

// A state is a rule with a dot before its next symbol, started at column reference. The states
// that want its rule's nonterminal are shared with every state predicted with it, and grow as
// later states in that column come to want it too.
type state struct {
	rule      *rule
	dot       int
	reference int
	data      any
	wantedBy  *[]*state
	left      *state
	child     any
	complete  bool
}

func newState(r *rule, dot, reference int, wantedBy *[]*state) *state {
	return &state{
		rule:      r,
		dot:       dot,
		reference: reference,
		data:      []any{},
		wantedBy:  wantedBy,
		complete:  dot == len(r.symbols),
	}
}

func (s *state) nextState(child any) *state {
	next := newState(s.rule, s.dot+1, s.reference, s.wantedBy)
	next.left = s
	next.child = child
	if next.complete {
		next.data = next.build()
	}
	return next
}

func (s *state) build() []any {
	var children []any
	for node := s; node.left != nil; node = node.left {
		children = append(children, node.child)
	}
	for i, j := 0, len(children)-1; i < j; i, j = i+1, j-1 {
		children[i], children[j] = children[j], children[i]
	}
	return children
}

func (s *state) finish() {
	if s.rule.postprocess != nil {
		s.data = s.rule.postprocess(s.data.([]any))
	}
}

func (s *state) rejected() bool {
	_, rejected := s.data.(rejection)
	return rejected
}

type column struct {
	index     int
	states    []*state
	wants     map[int]*[]*state
	scannable []*state
	completed map[int][]*state
}

func newColumn(index int) *column {
	return &column{index: index, wants: map[int]*[]*state{}, completed: map[int][]*state{}}
}

func (c *column) process() {
	for w := 0; w < len(c.states); w++ {
		s := c.states[w]
		if s.complete {
			s.finish()
			if s.rejected() {
				continue
			}
			wantedBy := *s.wantedBy
			for i := len(wantedBy) - 1; i >= 0; i-- {
				c.complete(wantedBy[i], s)
			}
			if s.reference == c.index {
				c.completed[s.rule.name] = append(c.completed[s.rule.name], s)
			}
			continue
		}
		expected := s.rule.symbols[s.dot].expects
		if expected == terminal {
			c.scannable = append(c.scannable, s)
			continue
		}
		if wants, ok := c.wants[expected]; ok {
			*wants = append(*wants, s)
			for _, nullable := range c.completed[expected] {
				c.complete(s, nullable)
			}
			continue
		}
		c.wants[expected] = &[]*state{s}
		c.predict(expected)
	}
}

func (c *column) predict(name int) {
	wantedBy := c.wants[name]
	for _, r := range rulesByName[name] {
		c.states = append(c.states, newState(r, 0, c.index, wantedBy))
	}
}

// rulesByName are the alternatives of each nonterminal, in the order of the rules.
var rulesByName = func() [][]*rule {
	byName := make([][]*rule, len(ruleNames))
	for i := range rules {
		byName[rules[i].name] = append(byName[rules[i].name], &rules[i])
	}
	return byName
}()

func (c *column) complete(left, right *state) {
	c.states = append(c.states, left.nextState(right.data))
}

// parse returns the values of every parse of the input, in nearley's order, and false when the
// input has no parse: when no state survives a code unit, where nearley throws.
func parse(input string) ([]any, bool) {
	current := newColumn(0)
	current.wants[start] = &[]*state{}
	current.predict(start)
	current.process()
	for index, unit := range utf16.Encode([]rune(input)) {
		next := newColumn(index + 1)
		token := codeUnitString(unit)
		for w := len(current.scannable) - 1; w >= 0; w-- {
			s := current.scannable[w]
			if s.rule.symbols[s.dot].accepts(unit) {
				next.states = append(next.states, s.nextState(token))
			}
		}
		next.process()
		if len(next.states) == 0 {
			return nil, false
		}
		current = next
	}
	var results []any
	for _, s := range current.states {
		if s.rule.name == start && s.complete && s.reference == 0 && !s.rejected() {
			results = append(results, s.data)
		}
	}
	return results, true
}
