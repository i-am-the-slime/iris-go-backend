// purescript-foldable-traversable 6.0.0's test foreigns in Test.Main (scripts/robust/suites.sh).
package Test_Main_ffi

type NEArray[A any] struct{ elements []A }

func ArrayFrom1UpTo(n int) []int {
	result := []int{}
	for i := 1; i <= n; i++ {
		result = append(result, i)
	}
	return result
}

func ArrayReplicate[A any](n int, x A) []A {
	result := []A{}
	for i := 1; i <= n; i++ {
		result = append(result, x)
	}
	return result
}

func MkNEArray[R any, A any](nothing R, just func(NEArray[A]) R, array []A) R {
	if len(array) > 0 {
		return just(NEArray[A]{elements: array})
	}
	return nothing
}

func FoldMap1NEArray[R any, A any](append func(R) func(R) R, f func(A) R, array NEArray[A]) R {
	accumulator := f(array.elements[0])
	for _, element := range array.elements[1:] {
		accumulator = append(accumulator)(f(element))
	}
	return accumulator
}
