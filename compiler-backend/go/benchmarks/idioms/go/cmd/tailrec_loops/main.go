package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(2000000, workload) }

func workload(n int) string {
	return strconv.Itoa(int(greatestDivisors(int(n)))) + " " + strconv.Itoa(int(countUp(int(n))))
}

func greatestDivisors(n int) int {
	var total int
	for i := int(1); i <= n; i++ {
		total += euclid(i, n+1-i)
	}
	return total
}

func euclid(a int, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func countUp(n int) int {
	var total int
	for i := int(1); i <= n; i++ {
		total += i % 7
	}
	return total
}
