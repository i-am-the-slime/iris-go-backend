package ffi

type Counter struct{ Total int }

var Zero = Counter{}

func (counter *Counter) Bump() int {
	counter.Total++
	return counter.Total
}

func Bumped(counter Counter) int { return counter.Bump() }

func Count(counter Counter) int { return counter.Total }
