// Data.BTreeChurn hand-written: the same persistent B-tree in Go (btree.go): every insert
// copies the path from the root, as the PureScript library's map does.
package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(400000, workload) }

func workload(n int) string {
	keys := harness.PseudoRandomArray(n)
	for i := range keys {
		keys[i] &= 0xFFFF
	}
	order := IntOrd(0)
	add := func(old, new int) int { return old + new }
	table := Empty[int, int]()
	for _, key := range keys {
		table = InsertWith(order, add, key, 1, table)
	}
	var hits int
	for _, key := range keys {
		if value, found := Lookup(order, key, table); found {
			hits += value
		}
	}
	total := FoldlWithKey(func(_ int, z int, v int) int { return z + v }, 0, table)
	return strconv.Itoa(Size(table)) + " " + strconv.Itoa(hits) + " " + strconv.Itoa(total)
}
