package ffi

import "math"

func Float32ToInt32(n float64) int32 {
	return int32(math.Float32bits(float32(n)))
}
