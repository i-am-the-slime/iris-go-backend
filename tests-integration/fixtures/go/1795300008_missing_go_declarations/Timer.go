package ffi

type Watch struct{ seconds float64 }

func Timer(seconds float64) Watch { return Watch{seconds} }

func Seconds(timer Watch) float64 { return timer.seconds }
