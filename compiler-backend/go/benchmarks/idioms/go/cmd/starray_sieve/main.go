package main

import (
	"math"
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(8000000, workload) }

func workload(n int) string {
	count := 0
	for _, flag := range sieve(n) {
		if flag {
			count++
		}
	}
	return strconv.Itoa(count)
}

func sieve(n int) []bool {
	flags := make([]bool, n+1)
	for i := range flags {
		flags[i] = true
	}
	flags[0], flags[1] = false, false
	limit := int(math.Floor(math.Sqrt(float64(n))))
	for i := 2; i <= limit; i++ {
		if flags[i] {
			for j := i * i; j <= n; j += i {
				flags[j] = false
			}
		}
	}
	return flags
}
