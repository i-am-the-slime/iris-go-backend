package ffi

func HandedOver[A any](value A) A { return value }

func Twice[A any](thunk func(struct{}) A) A {
	thunk(struct{}{})
	return thunk(struct{}{})
}

func Log(line string) { println(line) }
