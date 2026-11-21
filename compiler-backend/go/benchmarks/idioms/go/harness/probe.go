package harness

import (
	"strconv"

	"github.com/i-am-the-slime/iris-go/prim"
)

// Probe is Bench.Idiom.Simd.Probe: the length and three elements of a result.
func Probe(xs []float64) string {
	at := func(i int) float64 {
		if i >= 0 && i < len(xs) {
			return xs[i]
		}
		return 0
	}
	return strconv.Itoa(len(xs)) + " " + prim.ShowNumber(at(0)) + " " + prim.ShowNumber(at(len(xs)/2)) + " " + prim.ShowNumber(at(len(xs)-1))
}
