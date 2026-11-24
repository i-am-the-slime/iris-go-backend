package ffi

func PerformImpl[A any](effect func() A) A { return effect() }

func GuardedImpl[A any](handler func(string) A, action func() A) A {
	_ = handler
	return action()
}

func CombineImpl[A, B, C any](combine func(A) func(B) C, left func() A, right func() B) C {
	return combine(left())(right())
}

func ModifyImpl[T, B any](f func(int32) T, result func(T) B) B { return result(f(41)) }
