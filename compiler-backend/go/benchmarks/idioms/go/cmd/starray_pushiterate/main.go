package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(2000000, workload) }

func workload(n int) string {
	var values []int
	for i := 0; i < n; i++ {
		values = append(values, harness.Xorshift(int(i+1)))
	}
	for i := range values {
		values[i] &= 0xFFFF
	}
	snapshot := make([]int, len(values))
	copy(snapshot, values)
	var total int
	for _, value := range snapshot {
		total += value
	}
	return strconv.Itoa(int(total))
}
