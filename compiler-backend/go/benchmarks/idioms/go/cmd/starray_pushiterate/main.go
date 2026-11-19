package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(2000000, workload) }

func workload(n int) string {
	var values []int32
	for i := 0; i < n; i++ {
		values = append(values, harness.Xorshift(int32(i+1)))
	}
	for i := range values {
		values[i] &= 0xFFFF
	}
	snapshot := make([]int32, len(values))
	copy(snapshot, values)
	var total int32
	for _, value := range snapshot {
		total += value
	}
	return strconv.Itoa(int(total))
}
