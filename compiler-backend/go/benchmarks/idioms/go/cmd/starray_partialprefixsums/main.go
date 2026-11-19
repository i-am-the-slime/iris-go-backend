package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(4000000, workload) }

func workload(n int) string {
	sums := harness.PseudoRandomArray(n)
	for i := 1; i < len(sums); i++ {
		sums[i] += sums[i-1]
	}
	return strconv.Itoa(int(sums[n-1])) + " " + strconv.Itoa(int(sums[n/2]))
}
