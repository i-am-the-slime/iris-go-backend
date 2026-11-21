// Data.MapChurn on a hand-written persistent tree: the height-balanced binary tree of
// ordered-collections' Data.Map (Node height size key value left right, rebalanced by
// unsafeBalancedNode's single and double rotations), with direct int32 comparisons. Every insert
// copies the path from the root, as the PureScript library does. This is the fair baseline for
// the generated program; data_mapchurn's Go hash map is the data-structure ceiling.
package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(400000, workload) }

type node struct {
	left, right  *node
	height, size int32
	key, value   int32
}

func workload(n int) string {
	keys := harness.PseudoRandomArray(n)
	for i := range keys {
		keys[i] &= 0xFFFF
	}
	var table *node
	for _, key := range keys {
		table = insertWith(key, 1, table)
	}
	var hits int32
	for _, key := range keys {
		if value, found := lookup(key, table); found {
			hits += value
		}
	}
	return strconv.Itoa(int(size(table))) + " " + strconv.Itoa(int(hits)) + " " + strconv.Itoa(int(foldl(0, table)))
}

func insertWith(key, value int32, m *node) *node {
	if m == nil {
		return &node{height: 1, size: 1, key: key, value: value}
	}
	switch {
	case key < m.key:
		return balancedNode(m.key, m.value, insertWith(key, value, m.left), m.right)
	case key > m.key:
		return balancedNode(m.key, m.value, m.left, insertWith(key, value, m.right))
	default:
		return &node{height: m.height, size: m.size, key: key, value: m.value + value, left: m.left, right: m.right}
	}
}

func lookup(key int32, m *node) (int32, bool) {
	for m != nil {
		switch {
		case key < m.key:
			m = m.left
		case key > m.key:
			m = m.right
		default:
			return m.value, true
		}
	}
	return 0, false
}

func foldl(z int32, m *node) int32 {
	for m != nil {
		z = foldl(z, m.left) + m.value
		m = m.right
	}
	return z
}

func height(m *node) int32 {
	if m == nil {
		return 0
	}
	return m.height
}

func size(m *node) int32 {
	if m == nil {
		return 0
	}
	return m.size
}

func plainNode(key, value int32, l, r *node) *node {
	return &node{height: 1 + max(height(l), height(r)), size: 1 + size(l) + size(r), key: key, value: value, left: l, right: r}
}

func balancedNode(key, value int32, l, r *node) *node {
	lh, rh := height(l), height(r)
	switch {
	case rh > lh+1:
		return rotateLeft(key, value, l, r)
	case lh > rh+1:
		return rotateRight(key, value, l, r)
	default:
		return plainNode(key, value, l, r)
	}
}

func rotateLeft(key, value int32, l, r *node) *node {
	if rl := r.left; rl != nil && rl.height > height(r.right) {
		return plainNode(rl.key, rl.value, plainNode(key, value, l, rl.left), plainNode(r.key, r.value, rl.right, r.right))
	}
	return plainNode(r.key, r.value, plainNode(key, value, l, r.left), r.right)
}

func rotateRight(key, value int32, l, r *node) *node {
	if lr := l.right; lr != nil && height(l.left) <= lr.height {
		return plainNode(lr.key, lr.value, plainNode(l.key, l.value, l.left, lr.left), plainNode(key, value, lr.right, r))
	}
	return plainNode(l.key, l.value, l.left, plainNode(key, value, l.right, r))
}
