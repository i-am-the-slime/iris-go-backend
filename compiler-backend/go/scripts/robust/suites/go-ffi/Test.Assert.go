// purescript-assert 6.0.0's Test.Assert foreigns, for running library test suites under Go
// (scripts/robust/suites.sh). A failed assertion throws an Effect.Exception Error, as the JS
// foreign does.
package Test_Assert_ffi

import "github.com/i-am-the-slime/iris-go/exception"

func AssertImpl(message string, success bool) func() {
	return func() {
		if !success {
			panic(exception.NewError(message))
		}
	}
}

// CheckThrows reports whether applying the function to unit throws an Error. Anything else it
// throws (a Go runtime fault) propagates, as a non-Error throw does in JS.
func CheckThrows[A any](action func(struct{}) A) func() bool {
	return func() (threw bool) {
		defer func() {
			if recovered := recover(); recovered != nil {
				if _, isError := exception.AsError(recovered); !isError {
					panic(recovered)
				}
				threw = true
			}
		}()
		action(struct{}{})
		return false
	}
}
