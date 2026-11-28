package ffi

func Timed[A any](thunk func(struct{}) A) A { return thunk(struct{}{}) }

func Log(line string) { println(line) }
