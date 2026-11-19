package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(2000000, workload) }

func workload(n int) string {
	return strconv.Itoa(int(greatestDivisors(int32(n)))) + " " + strconv.Itoa(int(countUp(int32(n))))
}

func greatestDivisors(n int32) int32 {
	var total int32
	for i := int32(1); i <= n; i++ {
		total += euclid(i, n+1-i)
	}
	return total
}

func euclid(a int32, b int32) int32 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func countUp(n int32) int32 {
	var total int32
	for i := int32(1); i <= n; i++ {
		total += i % 7
	}
	return total
}
