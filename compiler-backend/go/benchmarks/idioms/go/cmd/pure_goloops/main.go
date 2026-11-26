package main

import (
	"strconv"
	"strings"

	"idioms.example/hand/harness"
)

func main() { harness.Run(3000000, workload) }

func workload(n int) string {
	values := harness.PseudoRandomArray(n)
	var sum int
	for _, value := range values {
		sum += value
	}
	parts := []string{
		strconv.Itoa(int(digitSums(int(n)))),
		strconv.Itoa(int(sum)),
		strconv.Itoa(int(indexedSum(values))),
		strconv.Itoa(int(indexedSum(values))),
		strconv.Itoa(int(fusedSum(int(n)))),
	}
	return strings.Join(parts, " ")
}

func digitSums(n int) int {
	var total int
	for i := int(1); i <= n; i++ {
		for x := i; x != 0; x /= 10 {
			total += x % 10
		}
	}
	return total
}

func indexedSum(values []int) int {
	var total int
	for i := 0; i < len(values); i++ {
		total += values[i]
	}
	return total
}

func fusedSum(n int) int {
	var total int
	for i := int(1); i <= n; i++ {
		total += i & 1023
	}
	return total
}
