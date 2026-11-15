// The Go side of ReproForeignDataInt (scripts/robust/suites.sh repro): a generic foreign data type.
package ReproForeignDataInt_ffi

type Box[A any] struct{ value A }

func MakeBox[A any](x A) Box[A] { return Box[A]{value: x} }

func EqBoxImpl[A any](eq func(A) func(A) bool, a Box[A], b Box[A]) bool { return eq(a.value)(b.value) }
