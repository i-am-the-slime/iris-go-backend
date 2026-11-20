package ffi

type Mutable []byte
type Frozen []byte

func New(n int32) Mutable { return make(Mutable, n) }
func Size(b Frozen) int32  { return int32(len(b)) }
