package ffi

func LengthArr[A any](xs []A) int32 { return int32(len(xs)) }

func UnsafeIndexArr[A any](xs []A, i int32) A { return xs[i] }
