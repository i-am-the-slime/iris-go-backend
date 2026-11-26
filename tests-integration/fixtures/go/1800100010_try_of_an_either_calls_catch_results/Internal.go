package ffi

import "github.com/i-am-the-slime/iris-go/exception"

func CatchImpl[A any](handler func(exception.Error) A, action func() A) A {
	result, failure, failed := attempt(action)
	if failed {
		return handler(failure)
	}
	return result
}

func CatchResultsImpl[A, F any](handler func(exception.Error) (A, F), action func() (A, F)) (A, F) {
	value, err, failure, failed := attemptResults(action)
	if failed {
		return handler(failure)
	}
	return value, err
}

func attempt[A any](action func() A) (result A, failure exception.Error, failed bool) {
	defer recoverInto(&failure, &failed)
	return action(), exception.Error{}, false
}

func attemptResults[A, F any](action func() (A, F)) (value A, err F, failure exception.Error, failed bool) {
	defer recoverInto(&failure, &failed)
	value, err = action()
	return value, err, exception.Error{}, false
}

func recoverInto(failure *exception.Error, failed *bool) {
	if recovered := recover(); recovered != nil {
		if caught, ok := exception.AsError(recovered); ok {
			*failure, *failed = caught, true
			return
		}
		panic(recovered)
	}
}
