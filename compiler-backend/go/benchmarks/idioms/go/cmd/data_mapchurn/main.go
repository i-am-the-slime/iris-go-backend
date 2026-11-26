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
	table := make(map[int]int)
	for _, key := range keys {
		table[key]++
	}
	var hits int
	for _, key := range keys {
		hits += table[key]
	}
	var total int
	for _, count := range table {
		total += count
	}
	return strconv.Itoa(len(table)) + " " + strconv.Itoa(int(hits)) + " " + strconv.Itoa(int(total))
}
