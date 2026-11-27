package ffi

type Pipe[A any] struct{ value A }

func NewPipe[A any](value A) Pipe[A] { return Pipe[A]{value: value} }

func OnTake[A, R any](pipe Pipe[A], taken func(A, bool) R) R { return taken(pipe.value, true) }

func Leaked(pipe any) int { return 1 }
