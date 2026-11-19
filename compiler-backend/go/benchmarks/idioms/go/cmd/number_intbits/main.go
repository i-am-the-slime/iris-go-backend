package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(3000000, workload) }

func workload(n int) string {
	seed := int32(88172645)
	var total int32
	for i := 0; i < n; i++ {
		seed = harness.Xorshift(seed)
		total += popCount(seed)
	}
	return strconv.Itoa(int(total))
}

func popCount(x int32) int32 {
	var count int32
	for v := uint32(x); v != 0; v >>= 1 {
		count += int32(v & 1)
	}
	return count
}
