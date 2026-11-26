// The hand-written reference for Data.BTreeMap: a persistent B-tree with wide nodes
// holding up to maxKeys entries in flat slices, so a lookup touches a few cache lines and a map
// of a million entries is four levels deep.
//
// Every operation returns a new map and leaves its argument as it was: a write copies the nodes
// on the path from the root to the entry (path copying) and shares everything else. Builders
// (FromEntries) own their tree until they return it and write into it in place.
//
// Keys are compared by an Ord[K]: Int, Number, String and Char have their own (distinct
// underlying types, so Go stencils and inlines each), any other key goes through the Ord
// dictionary's compare (ByCompare).
//
// The semantics are ordered-collections 3.2's: ascending iteration, a key that compares equal
// replaces the stored key on insert, insertWith passes the old value first, unionWith keeps the
// right map's key, and Show prints `(fromFoldable [(Tuple k v),...])`.
package main

import (
	"strings"

	"github.com/i-am-the-slime/iris-go/prim"
)

const (
	maxKeys = 31
	minKeys = maxKeys / 2
)

// Ord is a three-way comparison of keys: negative, zero or positive.
type Ord[K any] interface{ Compare(x K, y K) int }

type IntOrd int8

func (IntOrd) Compare(x int, y int) int {
	switch {
	case x < y:
		return -1
	case x > y:
		return 1
	}
	return 0
}

// NumberOrd compares as PureScript's Ord Number does: `<`, then `==`, and GT otherwise, so a NaN
// is greater than everything, itself included.
type NumberOrd int16

func (NumberOrd) Compare(x float64, y float64) int {
	switch {
	case x < y:
		return -1
	case x == y:
		return 0
	}
	return 1
}

// StringOrd compares by UTF-16 code units, as JavaScript does.
type StringOrd int32

func (StringOrd) Compare(x string, y string) int { return prim.CompareString(x, y) }

type CharOrd int64

func (CharOrd) Compare(x rune, y rune) int {
	switch {
	case x < y:
		return -1
	case x > y:
		return 1
	}
	return 0
}

// ByCompare is the Ord dictionary's compare, mapped to -1, 0 and 1.
type ByCompare[K any] func(K, K) int

func (compare ByCompare[K]) Compare(x K, y K) int { return compare(x, y) }

type node[K, V any] struct {
	keys     []K
	values   []V
	children []*node[K, V] // nil in a leaf, otherwise len(keys)+1
}

// Map is `Map k v`. The zero value is the empty map.
type Map[K, V any] struct {
	root *node[K, V]
	size int
}

func (n *node[K, V]) leaf() bool { return n.children == nil }

func (n *node[K, V]) clone() *node[K, V] {
	c := &node[K, V]{
		keys:   append(make([]K, 0, len(n.keys)+1), n.keys...),
		values: append(make([]V, 0, len(n.values)+1), n.values...),
	}
	if n.children != nil {
		c.children = append(make([]*node[K, V], 0, len(n.children)+1), n.children...)
	}
	return c
}

// search is the index of the first key not less than key, and whether it equals key.
func search[K, V any, O Ord[K]](o O, n *node[K, V], key K) (int, bool) {
	low, high := 0, len(n.keys)
	for low < high {
		middle := int(uint(low+high) >> 1)
		if o.Compare(n.keys[middle], key) < 0 {
			low = middle + 1
		} else {
			high = middle
		}
	}
	return low, low < len(n.keys) && o.Compare(n.keys[low], key) == 0
}

func Empty[K, V any]() Map[K, V] { return Map[K, V]{} }

func Singleton[K, V any](key K, value V) Map[K, V] {
	return Map[K, V]{&node[K, V]{keys: []K{key}, values: []V{value}}, 1}
}

func Size[K, V any](m Map[K, V]) int { return m.size }

func IsEmpty[K, V any](m Map[K, V]) bool { return m.size == 0 }

// Lookup is the value at key, if any.
func Lookup[K, V any, O Ord[K]](o O, key K, m Map[K, V]) (V, bool) {
	n := m.root
	for n != nil {
		i, found := search(o, n, key)
		if found {
			return n.values[i], true
		}
		if n.leaf() {
			break
		}
		n = n.children[i]
	}
	var zero V
	return zero, false
}

func Member[K, V any, O Ord[K]](o O, key K, m Map[K, V]) bool {
	_, found := Lookup(o, key, m)
	return found
}

// Insert sets key to value; a key already there is replaced along with its value.
func Insert[K, V any, O Ord[K]](o O, key K, value V, m Map[K, V]) Map[K, V] {
	return upsert(o, key, m, func(V, bool) V { return value })
}

// InsertWith combines an existing value with the new one as `combine old new`.
func InsertWith[K, V any, O Ord[K]](o O, combine func(V, V) V, key K, value V, m Map[K, V]) Map[K, V] {
	return upsert(o, key, m, func(old V, found bool) V {
		if found {
			return combine(old, value)
		}
		return value
	})
}

func upsert[K, V any, O Ord[K]](o O, key K, m Map[K, V], value func(V, bool) V) Map[K, V] {
	if m.root == nil {
		var zero V
		return Singleton(key, value(zero, false))
	}
	root, added := insertInto(o, m.root, key, value, false)
	return Map[K, V]{grow(root), m.size + added}
}

// insertInto writes key into n (a copy of it unless inPlace), and reports whether it added an
// entry. The result may hold maxKeys+1 keys, which its parent (or grow) splits.
func insertInto[K, V any, O Ord[K]](o O, n *node[K, V], key K, value func(V, bool) V, inPlace bool) (*node[K, V], int) {
	i, found := search(o, n, key)
	if !inPlace {
		n = n.clone()
	}
	if found {
		n.keys[i] = key
		n.values[i] = value(n.values[i], true)
		return n, 0
	}
	if n.leaf() {
		var zero V
		n.keys = insertAt(n.keys, i, key)
		n.values = insertAt(n.values, i, value(zero, false))
		return n, 1
	}
	child, added := insertInto(o, n.children[i], key, value, inPlace)
	n.children[i] = child
	if len(child.keys) > maxKeys {
		splitChild(n, i)
	}
	return n, added
}

// grow splits an overfull root under a new one.
func grow[K, V any](root *node[K, V]) *node[K, V] {
	if len(root.keys) <= maxKeys {
		return root
	}
	parent := &node[K, V]{children: []*node[K, V]{root}}
	splitChild(parent, 0)
	return parent
}

// splitChild splits n's overfull child i (which n owns) around its middle entry.
func splitChild[K, V any](n *node[K, V], i int) {
	child := n.children[i]
	middle := len(child.keys) / 2
	right := &node[K, V]{
		keys:   append([]K(nil), child.keys[middle+1:]...),
		values: append([]V(nil), child.values[middle+1:]...),
	}
	if !child.leaf() {
		right.children = append([]*node[K, V](nil), child.children[middle+1:]...)
		child.children = child.children[:middle+1:middle+1]
	}
	key, value := child.keys[middle], child.values[middle]
	child.keys = child.keys[:middle:middle]
	child.values = child.values[:middle:middle]
	n.keys = insertAt(n.keys, i, key)
	n.values = insertAt(n.values, i, value)
	n.children = insertAt(n.children, i+1, right)
}

func insertAt[T any](s []T, i int, x T) []T {
	var zero T
	s = append(s, zero)
	copy(s[i+1:], s[i:])
	s[i] = x
	return s
}

func removeAt[T any](s []T, i int) []T {
	copy(s[i:], s[i+1:])
	var zero T
	s[len(s)-1] = zero
	return s[:len(s)-1]
}

// Delete removes key, if it is there.
func Delete[K, V any, O Ord[K]](o O, key K, m Map[K, V]) Map[K, V] {
	_, out, found := Pop(o, key, m)
	if !found {
		return m
	}
	return out
}

// Pop removes key and returns its value.
func Pop[K, V any, O Ord[K]](o O, key K, m Map[K, V]) (V, Map[K, V], bool) {
	var zero V
	if m.root == nil || !Member(o, key, m) {
		return zero, m, false
	}
	root, value := deleteFrom(o, m.root, key)
	return value, shrink(root, m.size-1), true
}

func shrink[K, V any](root *node[K, V], size int) Map[K, V] {
	if size == 0 {
		return Map[K, V]{}
	}
	if len(root.keys) == 0 && !root.leaf() {
		root = root.children[0]
	}
	return Map[K, V]{root, size}
}

// deleteFrom removes key, which the subtree holds, from a copy of n. The copy may be left with
// fewer than minKeys keys, which its parent repairs.
func deleteFrom[K, V any, O Ord[K]](o O, n *node[K, V], key K) (*node[K, V], V) {
	i, found := search(o, n, key)
	n = n.clone()
	if n.leaf() {
		value := n.values[i]
		n.keys = removeAt(n.keys, i)
		n.values = removeAt(n.values, i)
		return n, value
	}
	if found {
		value := n.values[i]
		child, lastKey, lastValue := deleteLast(n.children[i])
		n.keys[i], n.values[i] = lastKey, lastValue
		n.children[i] = child
		repair(n, i)
		return n, value
	}
	child, value := deleteFrom(o, n.children[i], key)
	n.children[i] = child
	repair(n, i)
	return n, value
}

// deleteLast removes the greatest entry from a copy of n.
func deleteLast[K, V any](n *node[K, V]) (*node[K, V], K, V) {
	n = n.clone()
	last := len(n.keys) - 1
	if n.leaf() {
		key, value := n.keys[last], n.values[last]
		n.keys = n.keys[:last]
		n.values = n.values[:last]
		return n, key, value
	}
	child, key, value := deleteLast(n.children[last+1])
	n.children[last+1] = child
	repair(n, last+1)
	return n, key, value
}

// repair gives n's child i (a copy n owns) at least minKeys keys, borrowing from a sibling or
// merging with one. Siblings are copied before they change.
func repair[K, V any](n *node[K, V], i int) {
	child := n.children[i]
	if len(child.keys) >= minKeys {
		return
	}
	if i > 0 && len(n.children[i-1].keys) > minKeys {
		left := n.children[i-1].clone()
		n.children[i-1] = left
		last := len(left.keys) - 1
		child.keys = insertAt(child.keys, 0, n.keys[i-1])
		child.values = insertAt(child.values, 0, n.values[i-1])
		n.keys[i-1], n.values[i-1] = left.keys[last], left.values[last]
		left.keys, left.values = left.keys[:last], left.values[:last]
		if !left.leaf() {
			child.children = insertAt(child.children, 0, left.children[last+1])
			left.children = left.children[:last+1]
		}
		return
	}
	if i+1 < len(n.children) && len(n.children[i+1].keys) > minKeys {
		right := n.children[i+1].clone()
		n.children[i+1] = right
		child.keys = append(child.keys, n.keys[i])
		child.values = append(child.values, n.values[i])
		n.keys[i], n.values[i] = right.keys[0], right.values[0]
		right.keys, right.values = removeAt(right.keys, 0), removeAt(right.values, 0)
		if !right.leaf() {
			child.children = append(child.children, right.children[0])
			right.children = removeAt(right.children, 0)
		}
		return
	}
	if i+1 < len(n.children) {
		merge(n, i, child, n.children[i+1])
	} else {
		merge(n, i-1, n.children[i-1].clone(), child)
	}
}

// merge joins children i and i+1 of n with the key between them into left, which n owns.
func merge[K, V any](n *node[K, V], i int, left *node[K, V], right *node[K, V]) {
	left.keys = append(append(left.keys, n.keys[i]), right.keys...)
	left.values = append(append(left.values, n.values[i]), right.values...)
	if !left.leaf() {
		left.children = append(left.children, right.children...)
	}
	n.children[i] = left
	n.keys = removeAt(n.keys, i)
	n.values = removeAt(n.values, i)
	n.children = removeAt(n.children, i+1)
}

// Alter is `alter f key m`.
func Alter[K, V any, O Ord[K]](o O, f func(V, bool) (V, bool), key K, m Map[K, V]) Map[K, V] {
	old, found := Lookup(o, key, m)
	value, keep := f(old, found)
	switch {
	case keep:
		return Insert(o, key, value, m)
	case found:
		return Delete(o, key, m)
	}
	return m
}

// Update is `update f key m`: f decides the value of an existing key, or its removal.
func Update[K, V any, O Ord[K]](o O, f func(V) (V, bool), key K, m Map[K, V]) Map[K, V] {
	old, found := Lookup(o, key, m)
	if !found {
		return m
	}
	value, keep := f(old)
	if keep {
		return upsert(o, key, m, func(V, bool) V { return value })
	}
	return Delete(o, key, m)
}

// Each visits the entries in ascending key order until visit returns false.
func Each[K, V any](m Map[K, V], visit func(K, V) bool) {
	if m.root != nil {
		each(m.root, visit)
	}
}

func each[K, V any](n *node[K, V], visit func(K, V) bool) bool {
	for i := range n.keys {
		if !n.leaf() && !each(n.children[i], visit) {
			return false
		}
		if !visit(n.keys[i], n.values[i]) {
			return false
		}
	}
	return n.leaf() || each(n.children[len(n.keys)], visit)
}

// EachDescending visits the entries in descending key order until visit returns false.
func EachDescending[K, V any](m Map[K, V], visit func(K, V) bool) {
	if m.root != nil {
		eachDescending(m.root, visit)
	}
}

func eachDescending[K, V any](n *node[K, V], visit func(K, V) bool) bool {
	if !n.leaf() && !eachDescending(n.children[len(n.keys)], visit) {
		return false
	}
	for i := len(n.keys) - 1; i >= 0; i-- {
		if !visit(n.keys[i], n.values[i]) {
			return false
		}
		if !n.leaf() && !eachDescending(n.children[i], visit) {
			return false
		}
	}
	return true
}

// FoldlWithKey is `foldlWithIndex (\k acc v -> f k acc v) z m`.
func FoldlWithKey[K, V, A any](f func(K, A, V) A, z A, m Map[K, V]) A {
	Each(m, func(k K, v V) bool { z = f(k, z, v); return true })
	return z
}

// FoldrWithKey is `foldrWithIndex f z m`: the greatest key is combined first.
func FoldrWithKey[K, V, A any](f func(K, V, A) A, z A, m Map[K, V]) A {
	EachDescending(m, func(k K, v V) bool { z = f(k, v, z); return true })
	return z
}

// ToArrayBy is the entries in ascending key order, each made by pair.
func ToArrayBy[K, V, T any](pair func(K, V) T, m Map[K, V]) []T {
	out := make([]T, 0, m.size)
	Each(m, func(k K, v V) bool { out = append(out, pair(k, v)); return true })
	return out
}

// FromEntries builds a map from n entries in order, later ones winning, as `fromFoldable`.
// Entries already in strictly ascending key order are built bottom-up in O(n); otherwise the
// builder inserts into its own tree in place.
func FromEntries[K, V any, O Ord[K]](o O, n int, entry func(int) (K, V)) Map[K, V] {
	return FromEntriesWith(o, nil, n, entry)
}

// FromEntriesWith is `fromFoldableWith combine`: a repeated key keeps `combine new old`.
func FromEntriesWith[K, V any, O Ord[K]](o O, combine func(V, V) V, n int, entry func(int) (K, V)) Map[K, V] {
	keys, values := make([]K, n), make([]V, n)
	ascending := true
	for i := range n {
		keys[i], values[i] = entry(i)
		if i > 0 && ascending && o.Compare(keys[i-1], keys[i]) >= 0 {
			ascending = false
		}
	}
	if ascending {
		return FromAscending(keys, values)
	}
	var b Builder[K, V, O]
	b.ord = o
	for i := range n {
		b.InsertWith(combine, keys[i], values[i])
	}
	return b.Map()
}

// Builder is a map under construction that nothing else sees, so it writes in place.
type Builder[K, V any, O Ord[K]] struct {
	ord O
	m   Map[K, V]
}

func NewBuilder[K, V any, O Ord[K]](o O) *Builder[K, V, O] { return &Builder[K, V, O]{ord: o} }

// InsertWith sets key to value, or to `combine value old` when combine is non-nil and the key
// is there (fromFoldableWith's order).
func (b *Builder[K, V, O]) InsertWith(combine func(V, V) V, key K, value V) {
	choose := func(old V, found bool) V {
		if found && combine != nil {
			return combine(value, old)
		}
		return value
	}
	if b.m.root == nil {
		b.m = Singleton(key, value)
		return
	}
	root, added := insertInto(b.ord, b.m.root, key, choose, true)
	b.m = Map[K, V]{grow(root), b.m.size + added}
}

func (b *Builder[K, V, O]) Map() Map[K, V] { return b.m }

// FromAscending builds the map of keys in strictly ascending order bottom-up, in O(n). The
// slices become the map's.
func FromAscending[K, V any](keys []K, values []V) Map[K, V] {
	if len(keys) == 0 {
		return Map[K, V]{}
	}
	height := 0
	for capacity(height) < len(keys) {
		height++
	}
	return Map[K, V]{build(keys, values, height), len(keys)}
}

// capacity is the most entries a subtree of this height holds.
func capacity(height int) int {
	c := maxKeys
	for range height {
		c = c*(maxKeys+1) + maxKeys
		if c > 1<<40 {
			return c
		}
	}
	return c
}

func build[K, V any](keys []K, values []V, height int) *node[K, V] {
	if height == 0 {
		return &node[K, V]{keys: keys[:len(keys):len(keys)], values: values[:len(values):len(values)]}
	}
	below := capacity(height - 1)
	children := (len(keys) + 1 + below) / (below + 1) // ceil((n+1)/(below+1))
	if children < 2 {
		children = 2
	}
	n := &node[K, V]{
		keys:     make([]K, 0, children-1),
		values:   make([]V, 0, children-1),
		children: make([]*node[K, V], 0, children),
	}
	entries := len(keys) - (children - 1)
	start := 0
	for c := range children {
		size := entries / children
		if c < entries%children {
			size++
		}
		n.children = append(n.children, build(keys[start:start+size], values[start:start+size], height-1))
		start += size
		if c < children-1 {
			n.keys = append(n.keys, keys[start])
			n.values = append(n.values, values[start])
			start++
		}
	}
	return n
}

// UnionWith is `unionWith combine left right`: entries of both, `combine l r` where both have
// the key, which is then the right map's.
func UnionWith[K, V any, O Ord[K]](o O, combine func(V, V) V, left Map[K, V], right Map[K, V]) Map[K, V] {
	switch {
	case left.size == 0:
		return right
	case right.size == 0:
		return left
	}
	keys := make([]K, 0, left.size+right.size)
	values := make([]V, 0, left.size+right.size)
	mergeAscending(o, left, right,
		func(k K, v V) { keys, values = append(keys, k), append(values, v) },
		func(k K, v V) { keys, values = append(keys, k), append(values, v) },
		func(_ K, l V, k K, r V) { keys, values = append(keys, k), append(values, combine(l, r)) })
	return FromAscending(keys, values)
}

// IntersectionWith is `intersectionWith combine left right`.
func IntersectionWith[K, A, B, C any, O Ord[K]](o O, combine func(A, B) C, left Map[K, A], right Map[K, B]) Map[K, C] {
	var keys []K
	var values []C
	la, lb := ToArrayBy(entryOf[K, A], left), ToArrayBy(entryOf[K, B], right)
	i, j := 0, 0
	for i < len(la) && j < len(lb) {
		switch c := o.Compare(la[i].key, lb[j].key); {
		case c < 0:
			i++
		case c > 0:
			j++
		default:
			keys, values = append(keys, la[i].key), append(values, combine(la[i].value, lb[j].value))
			i, j = i+1, j+1
		}
	}
	return FromAscending(keys, values)
}

// Difference is the entries of left whose keys right lacks.
func Difference[K, V, W any, O Ord[K]](o O, left Map[K, V], right Map[K, W]) Map[K, V] {
	return FilterWithKey(func(k K, _ V) bool { return !Member(o, k, right) }, left)
}

type entry[K, V any] struct {
	key   K
	value V
}

func entryOf[K, V any](k K, v V) entry[K, V] { return entry[K, V]{k, v} }

func mergeAscending[K, V any, O Ord[K]](o O, left, right Map[K, V], onlyLeft, onlyRight func(K, V), both func(K, V, K, V)) {
	l, r := ToArrayBy(entryOf[K, V], left), ToArrayBy(entryOf[K, V], right)
	i, j := 0, 0
	for i < len(l) && j < len(r) {
		switch c := o.Compare(l[i].key, r[j].key); {
		case c < 0:
			onlyLeft(l[i].key, l[i].value)
			i++
		case c > 0:
			onlyRight(r[j].key, r[j].value)
			j++
		default:
			both(l[i].key, l[i].value, r[j].key, r[j].value)
			i, j = i+1, j+1
		}
	}
	for ; i < len(l); i++ {
		onlyLeft(l[i].key, l[i].value)
	}
	for ; j < len(r); j++ {
		onlyRight(r[j].key, r[j].value)
	}
}

// FilterWithKey keeps the entries keep accepts, in O(n).
func FilterWithKey[K, V any](keep func(K, V) bool, m Map[K, V]) Map[K, V] {
	var keys []K
	var values []V
	Each(m, func(k K, v V) bool {
		if keep(k, v) {
			keys, values = append(keys, k), append(values, v)
		}
		return true
	})
	if len(keys) == m.size {
		return m
	}
	return FromAscending(keys, values)
}

// MapMaybeWithKey is `mapMaybeWithKey f m`.
func MapMaybeWithKey[K, A, B any](f func(K, A) (B, bool), m Map[K, A]) Map[K, B] {
	var keys []K
	var values []B
	Each(m, func(k K, a A) bool {
		if b, keep := f(k, a); keep {
			keys, values = append(keys, k), append(values, b)
		}
		return true
	})
	return FromAscending(keys, values)
}

// MapWithKey is `mapWithIndex f m`, keeping the tree's shape.
func MapWithKey[K, A, B any](f func(K, A) B, m Map[K, A]) Map[K, B] {
	if m.root == nil {
		return Map[K, B]{}
	}
	return Map[K, B]{mapNode(f, m.root), m.size}
}

func mapNode[K, A, B any](f func(K, A) B, n *node[K, A]) *node[K, B] {
	out := &node[K, B]{keys: n.keys, values: make([]B, len(n.values))}
	for i := range n.keys {
		if !n.leaf() {
			if out.children == nil {
				out.children = make([]*node[K, B], len(n.children))
			}
			out.children[i] = mapNode(f, n.children[i])
		}
		out.values[i] = f(n.keys[i], n.values[i])
	}
	if !n.leaf() {
		out.children[len(n.keys)] = mapNode(f, n.children[len(n.keys)])
	}
	return out
}

// FindMin and FindMax are the least and greatest entries.
func FindMin[K, V any](m Map[K, V]) (K, V, bool) {
	n := m.root
	if n == nil {
		var k K
		var v V
		return k, v, false
	}
	for !n.leaf() {
		n = n.children[0]
	}
	return n.keys[0], n.values[0], true
}

func FindMax[K, V any](m Map[K, V]) (K, V, bool) {
	n := m.root
	if n == nil {
		var k K
		var v V
		return k, v, false
	}
	for !n.leaf() {
		n = n.children[len(n.children)-1]
	}
	last := len(n.keys) - 1
	return n.keys[last], n.values[last], true
}

// LookupLE is the entry with the greatest key not above key; LookupLT, LookupGE and LookupGT
// likewise.
func LookupLE[K, V any, O Ord[K]](o O, key K, m Map[K, V]) (K, V, bool) {
	return nearest(o, key, m, true, true)
}

func LookupLT[K, V any, O Ord[K]](o O, key K, m Map[K, V]) (K, V, bool) {
	return nearest(o, key, m, true, false)
}

func LookupGE[K, V any, O Ord[K]](o O, key K, m Map[K, V]) (K, V, bool) {
	return nearest(o, key, m, false, true)
}

func LookupGT[K, V any, O Ord[K]](o O, key K, m Map[K, V]) (K, V, bool) {
	return nearest(o, key, m, false, false)
}

func nearest[K, V any, O Ord[K]](o O, key K, m Map[K, V], below bool, equal bool) (K, V, bool) {
	var bestKey K
	var bestValue V
	have := false
	for n := m.root; n != nil; {
		i, found := search(o, n, key)
		if found && equal {
			return n.keys[i], n.values[i], true
		}
		switch {
		case below && i > 0:
			bestKey, bestValue, have = n.keys[i-1], n.values[i-1], true
		case !below && found && i+1 < len(n.keys):
			bestKey, bestValue, have = n.keys[i+1], n.values[i+1], true
		case !below && !found && i < len(n.keys):
			bestKey, bestValue, have = n.keys[i], n.values[i], true
		}
		if n.leaf() {
			break
		}
		if found && !below {
			n = n.children[i+1]
		} else {
			n = n.children[i]
		}
	}
	return bestKey, bestValue, have
}

// Submap is `submap low high m`, either bound optional and inclusive.
func Submap[K, V any, O Ord[K]](o O, low K, hasLow bool, high K, hasHigh bool, m Map[K, V]) Map[K, V] {
	return FilterWithKey(func(k K, _ V) bool {
		return (!hasLow || o.Compare(low, k) <= 0) && (!hasHigh || o.Compare(k, high) <= 0)
	}, m)
}

// Equal is the Eq instance: same size and pairwise equal entries in order.
func Equal[K, V any](equalKey func(K, K) bool, equalValue func(V, V) bool, x Map[K, V], y Map[K, V]) bool {
	if x.size != y.size {
		return false
	}
	xs, ys := ToArrayBy(entryOf[K, V], x), ToArrayBy(entryOf[K, V], y)
	for i := range xs {
		if !equalKey(xs[i].key, ys[i].key) || !equalValue(xs[i].value, ys[i].value) {
			return false
		}
	}
	return true
}

// Compare is the Ord instance: entries in order, key then value, a prefix first.
func Compare[K, V any](compareKey func(K, K) int, compareValue func(V, V) int, x Map[K, V], y Map[K, V]) int {
	xs, ys := ToArrayBy(entryOf[K, V], x), ToArrayBy(entryOf[K, V], y)
	for i := 0; i < len(xs) && i < len(ys); i++ {
		if c := compareKey(xs[i].key, ys[i].key); c != 0 {
			return c
		}
		if c := compareValue(xs[i].value, ys[i].value); c != 0 {
			return c
		}
	}
	switch {
	case len(xs) < len(ys):
		return -1
	case len(xs) > len(ys):
		return 1
	}
	return 0
}

// Show is the Show instance: `(fromFoldable [(Tuple k v),...])`.
func Show[K, V any](showKey func(K) string, showValue func(V) string, m Map[K, V]) string {
	var b strings.Builder
	b.WriteString("(fromFoldable [")
	first := true
	Each(m, func(k K, v V) bool {
		if !first {
			b.WriteByte(',')
		}
		first = false
		b.WriteString("(Tuple ")
		b.WriteString(showKey(k))
		b.WriteByte(' ')
		b.WriteString(showValue(v))
		b.WriteByte(')')
		return true
	})
	b.WriteString("])")
	return b.String()
}
