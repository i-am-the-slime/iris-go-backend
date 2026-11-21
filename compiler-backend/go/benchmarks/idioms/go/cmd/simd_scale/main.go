package main

import (
	"idioms.example/hand/harness"
)

func main() {
	left, _, _ := harness.Signal()
	harness.Run(3, func(k int) string { return harness.Probe(scale(left, float64(k))) })
}

func scale(xs []float64, k float64) []float64 {
	out := make([]float64, len(xs))
	for i, x := range xs {
		out[i] = x * k
	}
	return out
}
