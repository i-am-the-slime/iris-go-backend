package ffi

type Box[A any] struct {
	value any
}

func NewBox[A any](value A) Box[A] { return Box[A]{value: value} }

func ReadBox[A any](box Box[A]) A { return box.value.(A) }
