// purescript-bigints' Data.BigInt foreign imports (bigints 7.0.1, over the `big-integer` npm
// package), ported to math/big for the compatibility corpus. big-integer's `divide` and `mod`
// truncate toward zero, like Go's Quo and Rem.
package Data_BigInt_ffi

import (
	"math"
	"math/big"
)

type BigInt struct{ value *big.Int }

func wrap(value *big.Int) BigInt { return BigInt{value: value} }

func FromInt(n int) BigInt { return wrap(big.NewInt(int64(n))) }

func FromTypeLevelInt(text string) BigInt {
	value, _ := new(big.Int).SetString(text, 10)
	return wrap(value)
}

func ToBase(base int, x BigInt) string { return x.value.Text(base) }

func ToNumber(x BigInt) float64 {
	value, _ := new(big.Float).SetInt(x.value).Float64()
	return value
}

func BiAdd(x BigInt, y BigInt) BigInt { return wrap(new(big.Int).Add(x.value, y.value)) }
func BiMul(x BigInt, y BigInt) BigInt { return wrap(new(big.Int).Mul(x.value, y.value)) }
func BiSub(x BigInt, y BigInt) BigInt { return wrap(new(big.Int).Sub(x.value, y.value)) }
func BiDiv(x BigInt, y BigInt) BigInt { return wrap(new(big.Int).Quo(x.value, y.value)) }
func BiMod(x BigInt, y BigInt) BigInt { return wrap(new(big.Int).Rem(x.value, y.value)) }

func BiEquals(x BigInt, y BigInt) bool { return x.value.Cmp(y.value) == 0 }
func BiCompare(x BigInt, y BigInt) int { return x.value.Cmp(y.value) }

func Abs(x BigInt) BigInt { return wrap(new(big.Int).Abs(x.value)) }
func Even(x BigInt) bool  { return x.value.Bit(0) == 0 }
func Odd(x BigInt) bool   { return x.value.Bit(0) == 1 }

func Pow(x BigInt, y BigInt) BigInt {
	if y.value.Sign() < 0 {
		return wrap(new(big.Int))
	}
	return wrap(new(big.Int).Exp(x.value, y.value, nil))
}

func Not(x BigInt) BigInt           { return wrap(new(big.Int).Not(x.value)) }
func Or(x BigInt, y BigInt) BigInt  { return wrap(new(big.Int).Or(x.value, y.value)) }
func Xor(x BigInt, y BigInt) BigInt { return wrap(new(big.Int).Xor(x.value, y.value)) }
func And(x BigInt, y BigInt) BigInt { return wrap(new(big.Int).And(x.value, y.value)) }

func Shl(x BigInt, n float64) BigInt {
	if n < 0 {
		return Shr(x, -n)
	}
	return wrap(new(big.Int).Lsh(x.value, uint(math.Trunc(n))))
}

func Shr(x BigInt, n float64) BigInt {
	if n < 0 {
		return Shl(x, -n)
	}
	return wrap(new(big.Int).Rsh(x.value, uint(math.Trunc(n))))
}
