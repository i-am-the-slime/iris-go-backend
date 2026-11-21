package harness

// Signal is the SIMD benchmarks' input: two buffers of ten million samples in [-1, 1] and ten
// million Ints in [0, 1000), built before the timed workload like the PureScript side's top-level
// arrays.
func Signal() (left, right []float64, counts []int32) {
	const size = 10000000
	left, right, counts = make([]float64, size), make([]float64, size), make([]int32, size)
	for i := range size {
		index := int32(i + 1)
		left[i] = float64(euclideanMod(Xorshift(index+1), 2001)-1000) * 0.001
		right[i] = float64(euclideanMod(Xorshift(index+7), 2001)-1000) * 0.001
		counts[i] = euclideanMod(Xorshift(index+3), 1000)
	}
	return left, right, counts
}

func euclideanMod(x, y int32) int32 {
	return (x%y + y) % y
}
