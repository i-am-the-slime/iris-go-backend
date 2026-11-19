package main

import (
	"strconv"
	"strings"

	"idioms.example/hand/harness"
)

func main() { harness.Run(3000000, workload) }

func workload(n int) string {
	values := harness.PseudoRandomArray(n)
	var sum int32
	for _, value := range values {
		sum += value
	}
	parts := []string{
		strconv.Itoa(int(digitSums(int32(n)))),
		strconv.Itoa(int(sum)),
		strconv.Itoa(int(indexedSum(values))),
		strconv.Itoa(int(indexedSum(values))),
		strconv.Itoa(int(fusedSum(int32(n)))),
	}
	return strings.Join(parts, " ")
}

func digitSums(n int32) int32 {
	var total int32
	for i := int32(1); i <= n; i++ {
		for x := i; x != 0; x /= 10 {
			total += x % 10
		}
	}
	return total
}

func indexedSum(values []int32) int32 {
	var total int32
	for i := 0; i < len(values); i++ {
		total += values[i]
	}
	return total
}

func fusedSum(n int32) int32 {
	var total int32
	for i := int32(1); i <= n; i++ {
		total += i & 1023
	}
	return total
}
