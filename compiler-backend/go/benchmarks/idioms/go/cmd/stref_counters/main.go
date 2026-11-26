package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(10000000, workload) }

func workload(n int) string {
	var total int
	for i := 0; i < n; i++ {
		total += int(i) & 7
	}
	for i := 0; i < n; i++ {
		total += int(i) % 3
	}
	for _, value := range harness.PseudoRandomArray(n / 10) {
		total += value & 1
	}
	return strconv.Itoa(int(total))
}
