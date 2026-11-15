// purescript-quickcheck 8.0.1's Test.QuickCheck.Gen foreign, for running library test suites under
// Go (scripts/robust/suites.sh). Coarbitrary Number perturbs the seed with the bits of the
// number stored as a float32, as the JS foreign does through a shared ArrayBuffer.
package Test_QuickCheck_Gen_ffi

import "math"

func Float32ToInt32(n float64) int32 {
	if math.IsNaN(n) {
		// A Float32Array stores every NaN as the canonical quiet NaN.
		return 0x7fc00000
	}
	return int32(math.Float32bits(float32(n)))
}
