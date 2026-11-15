// purescript-prelude 6.0.2's test foreigns in Test.Main (scripts/robust/suites.sh), with the same
// show cases as test/Test/Main.js.
package Test_Main_ffi

import (
	"math"

	"github.com/i-am-the-slime/purs-backend-go/go-support/exception"
)

func TestNumberShow(showNumber func(float64) string, _ struct{}) struct{} {
	cases := []struct {
		number   float64
		expected string
	}{
		{0.0, "0.0"}, {1.0, "1.0"}, {-1.0, "-1.0"}, {500.0, "500.0"},
		{1e10, "10000000000.0"}, {1e10 + 0.5, "10000000000.5"}, {-1e10, "-10000000000.0"}, {-1e10 - 0.5, "-10000000000.5"},
		{1e21, "1e+21"}, {1e-21, "1e-21"},
		{1.5e21, "1.5e+21"}, {1.5e-10, "1.5e-10"},
		{math.NaN(), "NaN"}, {math.Inf(1), "Infinity"}, {math.Inf(-1), "-Infinity"},
	}
	for _, c := range cases {
		if actual := showNumber(c.number); actual != c.expected {
			panic(exception.NewError("expected " + c.expected + ", got: " + actual + "."))
		}
	}
	return struct{}{}
}

func MakeArray(length int) []int {
	array := make([]int, 0, max(length, 0))
	for i := 0; i < length; i++ {
		array = append(array, i)
	}
	return array
}
