package ffi

type Box[A any] struct{ value A }

func Put[A any](value A) Box[A] { return Box[A]{value: value} }

func Get[A any](box Box[A]) A { return box.value }

func Sealed(value any) Box[int] { return Box[int]{value: 7} }
