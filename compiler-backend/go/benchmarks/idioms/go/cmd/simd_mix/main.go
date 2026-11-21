package main

import (
	"idioms.example/hand/harness"
)

func main() {
	left, right, _ := harness.Signal()
	harness.Run(8, func(n int) string {
		leftGain := float64(n) * 0.1
		return harness.Probe(mix(left, right, leftGain, 1.0-leftGain))
	})
}

func mix(left, right []float64, leftGain, rightGain float64) []float64 {
	out := make([]float64, min(len(left), len(right)))
	for i := range out {
		out[i] = min(1.0, max(-1.0, leftGain*left[i]+rightGain*right[i]))
	}
	return out
}
