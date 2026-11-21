package ffi

type Reply struct{}

type Route struct {
	Path     string
	Handle   func(string, string, Reply)
	Done     func(string)
	Prefixed func(string) func(string, Reply)
}

func Serve(route Route) {
	route.Handle("world", "hi", Reply{})
	route.Done(route.Path)
	route.Prefixed("p")("x", Reply{})
}

func Call(handle func(string, string, Reply)) { handle("a", "b", Reply{}) }

var BuiltIn = Route{
	Path:     "/built-in",
	Handle:   func(string, string, Reply) {},
	Done:     func(string) {},
	Prefixed: func(string) func(string, Reply) { return func(string, Reply) {} },
}

var NoReply = Reply{}
