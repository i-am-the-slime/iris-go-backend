package ffi

func OutcomeImpl[R any](failed func(int32) func(string) R, finished R, succeeded bool) R {
	if succeeded {
		return finished
	}
	return failed(7)("connection reset")
}
