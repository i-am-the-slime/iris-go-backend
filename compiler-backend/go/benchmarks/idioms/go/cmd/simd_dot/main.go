package main

import (
	"github.com/i-am-the-slime/iris-go/prim"

	"idioms.example/hand/harness"
)

func main() {
	left, right, _ := harness.Signal()
	harness.Run(0, func(int) string { return prim.ShowNumber(dot(left, right)) })
}

func dot(xs, ys []float64) float64 {
	var total float64
	for i := range min(len(xs), len(ys)) {
		total += xs[i] * ys[i]
	}
	return total
}
