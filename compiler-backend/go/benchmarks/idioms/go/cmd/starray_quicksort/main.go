package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(400000, workload) }

func workload(n int) string {
	values := harness.PseudoRandomArray(n)
	quickSort(values, 0, len(values)-1)
	var sum int
	for _, value := range values {
		sum += value
	}
	return strconv.Itoa(int(sum)) + " " + strconv.Itoa(int(values[n/2]))
}

func quickSort(values []int, low int, high int) {
	if low >= high {
		return
	}
	pivot := values[high]
	boundary := low
	for j := low; j < high; j++ {
		if values[j] < pivot {
			values[boundary], values[j] = values[j], values[boundary]
			boundary++
		}
	}
	values[boundary], values[high] = values[high], values[boundary]
	quickSort(values, low, boundary-1)
	quickSort(values, boundary+1, high)
}
