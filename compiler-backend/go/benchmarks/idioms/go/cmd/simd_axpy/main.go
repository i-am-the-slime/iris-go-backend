package main

import (
	"idioms.example/hand/harness"
)

func main() {
	left, right, _ := harness.Signal()
	harness.Run(3, func(n int) string { return harness.Probe(axpy(float64(n)*0.5, left, right)) })
}

func axpy(a float64, xs, ys []float64) []float64 {
	out := make([]float64, min(len(xs), len(ys)))
	for i := range out {
		out[i] = a*xs[i] + ys[i]
	}
	return out
}
