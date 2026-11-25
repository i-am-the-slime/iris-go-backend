package ffi

type Counter struct{ Total int32 }

var Zero = Counter{}

func (counter *Counter) Bump() int32 {
	counter.Total++
	return counter.Total
}

func Bumped(counter Counter) int32 { return counter.Bump() }

func Count(counter Counter) int32 { return counter.Total }
