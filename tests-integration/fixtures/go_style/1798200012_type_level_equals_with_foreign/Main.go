package ffi

func LengthArr[A any](xs []A) int { return len(xs) }

func UnsafeIndexArr[A any](xs []A, i int) A { return xs[i] }
