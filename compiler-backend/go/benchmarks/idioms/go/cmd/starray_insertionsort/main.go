package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(10000, workload) }

func workload(n int) string {
	values := harness.PseudoRandomArray(n)
	insertionSort(values)
	var sum int32
	for _, value := range values {
		sum += value
	}
	return strconv.Itoa(int(sum)) + " " + strconv.Itoa(int(values[n/2]))
}

func insertionSort(values []int32) {
	for i := 1; i < len(values); i++ {
		current := values[i]
		j := i - 1
		for j >= 0 && values[j] > current {
			values[j+1] = values[j]
			j--
		}
		values[j+1] = current
	}
}
