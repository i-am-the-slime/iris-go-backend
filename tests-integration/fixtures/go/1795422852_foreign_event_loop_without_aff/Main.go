package ffi

import "github.com/i-am-the-slime/iris-go/eventloop"

func OnAnotherGoroutine(callback func()) {
	retire := eventloop.Hold()
	go func() {
		eventloop.Turn(callback)
		retire()
	}()
}
