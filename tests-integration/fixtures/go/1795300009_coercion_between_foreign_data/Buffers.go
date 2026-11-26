package ffi

type Mutable []byte
type Frozen []byte

func New(n int) Mutable { return make(Mutable, n) }
func Size(b Frozen) int  { return len(b) }
