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
	table := make(map[int32]int32)
	for _, key := range keys {
		table[key]++
	}
	var hits int32
	for _, key := range keys {
		hits += table[key]
	}
	var total int32
	for _, count := range table {
		total += count
	}
	return strconv.Itoa(len(table)) + " " + strconv.Itoa(int(hits)) + " " + strconv.Itoa(int(total))
}
