package ffi

import "fmt"

type Settings struct {
	Greeting func(string) func(string) string
}

type Routes struct {
	Handle   func(string, string, func(string))
	Add      func(int) func(int) int
	Each     []func(string) func(string)
	Settings Settings
}

type Hooks struct {
	Route func(string) func(string, func(string))
	Fold  func(func(float64) func(float64) float64) float64
}

func Serve(routes Routes) {
	routes.Handle("alice", "hi", func(reply string) { fmt.Println(reply) })
	fmt.Println(routes.Add(1)(2))
	for _, each := range routes.Each {
		each("a")("b")
	}
	fmt.Println(routes.Settings.Greeting("hello")("alice"))
}

func InstallHooks() Hooks {
	return Hooks{
		Route: func(name string) func(string, func(string)) {
			return func(body string, reply func(string)) { reply(name + " " + body) }
		},
		Fold: func(step func(float64) func(float64) float64) float64 { return step(1)(2) },
	}
}

func Log(line string) { fmt.Println(line) }
