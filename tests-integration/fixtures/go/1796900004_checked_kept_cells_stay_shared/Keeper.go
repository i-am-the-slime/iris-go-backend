package ffi

var stored any

func Keep[A any](value A) int32 {
	stored = value
	return 1
}

func Kept[A any]() A { return stored.(A) }
