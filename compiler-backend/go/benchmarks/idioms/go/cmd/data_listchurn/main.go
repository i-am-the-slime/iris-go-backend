package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(2000000, workload) }

func workload(n int) string {
	values := make([]int32, 0, n)
	for i := 0; i < n; i++ {
		values = append(values, harness.Xorshift(int32(i+1)))
	}
	var evens []int32
	for _, value := range values {
		if value&1 == 0 {
			evens = append(evens, value)
		}
	}
	var sum int32
	for _, value := range evens {
		sum += value * 3
	}
	return strconv.Itoa(len(evens)) + " " + strconv.Itoa(int(sum)) + " (Just " + strconv.Itoa(int(values[0])) + ")"
}
