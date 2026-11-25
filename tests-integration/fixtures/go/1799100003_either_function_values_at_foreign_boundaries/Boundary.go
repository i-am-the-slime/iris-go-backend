package ffi

func RepeatImpl[A any](times int32, action func() A) []A {
	results := make([]A, 0, times)
	for range times {
		results = append(results, action())
	}
	return results
}

func KeepImpl[A any](value A) A { return value }
