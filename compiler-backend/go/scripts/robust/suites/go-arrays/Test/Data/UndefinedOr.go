// purescript-arrays 7.3.0's test foreigns in Test.Data.UndefinedOr (scripts/robust/suites.sh).
package Test_Data_UndefinedOr_ffi

type UndefinedOr[A any] struct {
	value   A
	defined bool
}

func Undefined[A any]() UndefinedOr[A] { return UndefinedOr[A]{} }

func Defined[A any](x A) UndefinedOr[A] { return UndefinedOr[A]{value: x, defined: true} }

func EqUndefinedOrImpl[A any](eq func(A) func(A) bool, a UndefinedOr[A], b UndefinedOr[A]) bool {
	return (!a.defined && !b.defined) || (a.defined && b.defined && eq(a.value)(b.value))
}

func CompareUndefinedOrImpl[O any, A any](lt O, eq O, gt O, compare func(A) func(A) O, a UndefinedOr[A], b UndefinedOr[A]) O {
	switch {
	case !a.defined && !b.defined:
		return eq
	case !a.defined:
		return lt
	case !b.defined:
		return gt
	default:
		return compare(a.value)(b.value)
	}
}
