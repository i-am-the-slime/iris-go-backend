package ffi

type Repeated[A any] []A

func Empty[A any]() Repeated[A] { return nil }

func SnocImpl[A any](items Repeated[A], item A) Repeated[A] { return append(items, item) }

func Freeze[A any](items Repeated[A]) []A { return items }

func Length[A any](items Repeated[A]) int { return len(items) }

func IndexOrImpl[A any](fallback A, index int, items Repeated[A]) A {
	if index < 0 || int(index) >= len(items) {
		return fallback
	}
	return items[index]
}

func Describe[A any](value A) string {
	switch any(value).(type) {
	case int:
		return "an int"
	default:
		return "something else"
	}
}
