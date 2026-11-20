// purescript-prelude 6.0.2's test foreign Test.Utils.throwErr (scripts/robust/suites.sh).
package Test_Utils_ffi

import "github.com/i-am-the-slime/iris-go/exception"

func ThrowErr(message string, _ struct{}) struct{} {
	panic(exception.NewError(message))
}
