package main

import (
	"math"

	"github.com/i-am-the-slime/iris-go/prim"

	"idioms.example/hand/harness"
)

func main() {
	left, _, _ := harness.Signal()
	harness.Run(0, func(int) string { return prim.ShowNumber(maximum(left)) })
}

func maximum(xs []float64) float64 {
	best := math.Inf(-1)
	for _, x := range xs {
		if x > best {
			best = x
		}
	}
	return best
}
