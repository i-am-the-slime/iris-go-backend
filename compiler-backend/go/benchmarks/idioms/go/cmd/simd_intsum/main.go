package main

import (
	"github.com/i-am-the-slime/iris-go/prim"

	"idioms.example/hand/harness"
)

func main() {
	_, _, counts := harness.Signal()
	harness.Run(0, func(int) string {
		return prim.ShowInt(sum(counts)) + " " + prim.ShowInt(maximum(counts))
	})
}

func sum(xs []int) int {
	var total int
	for _, x := range xs {
		total += x
	}
	return total
}

func maximum(xs []int) int {
	var best int
	for _, x := range xs {
		best = max(best, x)
	}
	return best
}
