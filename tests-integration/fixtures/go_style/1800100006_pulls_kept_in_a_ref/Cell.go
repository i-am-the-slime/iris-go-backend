package ffi

import "sync/atomic"

type Cell[A any] = *cell[A]

type cell[A any] struct {
	value atomic.Pointer[A]
}

func (ref *cell[A]) Load() A { return *ref.value.Load() }

func (ref *cell[A]) Store(value A) { ref.value.Store(&value) }

func New[A any](value A) *cell[A] {
	ref := &cell[A]{}
	ref.value.Store(&value)
	return ref
}

func Read[A any](ref *cell[A]) A { return ref.Load() }

func Write[A any](ref *cell[A], value A) { ref.Store(value) }
