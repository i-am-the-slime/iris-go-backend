package main

import (
	"github.com/i-am-the-slime/iris-go/prim"

	"idioms.example/hand/harness"
)

func main() {
	left, _, _ := harness.Signal()
	harness.Run(0, func(int) string { return prim.ShowNumber(sum(left)) })
}

func sum(xs []float64) float64 {
	var total float64
	for _, x := range xs {
		total += x
	}
	return total
}
