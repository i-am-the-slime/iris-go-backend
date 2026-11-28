package ffi

func Timed[A any](thunk func(struct{}) A) A { return thunk(struct{}{}) }
