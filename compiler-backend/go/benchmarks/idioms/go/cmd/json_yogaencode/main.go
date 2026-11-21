package main

import (
	"strconv"

	"idioms.example/hand/harness"
	"idioms.example/hand/jsondoc"
)

var doc = jsondoc.New(10000)

func main() { harness.Run(8, workload) }

func workload(n int) string {
	total := 0
	for i := 1; i <= n; i++ {
		versioned := doc
		versioned.Version = i
		total += jsondoc.Units(jsondoc.Marshal(versioned)) - i
	}
	return strconv.Itoa(total)
}
