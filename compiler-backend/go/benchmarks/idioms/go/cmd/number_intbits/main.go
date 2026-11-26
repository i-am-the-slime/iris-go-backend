package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(3000000, workload) }

func workload(n int) string {
	seed := int(88172645)
	var total int
	for i := 0; i < n; i++ {
		seed = harness.Xorshift(seed)
		total += popCount(seed)
	}
	return strconv.Itoa(int(total))
}

func popCount(x int) int {
	var count int
	for v := uint(x); v != 0; v >>= 1 {
		count += int(v & 1)
	}
	return count
}
