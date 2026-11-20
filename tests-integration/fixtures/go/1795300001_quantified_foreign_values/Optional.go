package ffi

type Optional[A any] struct {
	value   A
	present bool
}

type Pair[A any, B any] struct {
	first  A
	second B
	size   int
}

func Absent[A any]() Optional[A] { return Optional[A]{} }

func Present[A any](value A) Optional[A] { return Optional[A]{value: value, present: true} }

func WithDefault[A any](fallback A, optional Optional[A]) A {
	if optional.present {
		return optional.value
	}
	return fallback
}

func EmptyArray[A any]() []A { return []A{} }

func SwappedPair[A any, B any](a A, b B) Pair[B, A] {
	return Pair[B, A]{first: b, second: a, size: 2}
}

func EmptySwappedPair[A any, B any]() Pair[B, A] { return Pair[B, A]{} }

func PairSize[A any, B any](pair Pair[A, B]) int { return pair.size }

func NewCounter[A any]() Optional[A] { return Optional[A]{} }
