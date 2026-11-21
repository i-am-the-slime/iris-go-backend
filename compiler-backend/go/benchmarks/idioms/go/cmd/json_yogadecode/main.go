package main

import (
	"encoding/json"
	"strconv"

	"idioms.example/hand/harness"
	"idioms.example/hand/jsondoc"
)

var input = jsondoc.Marshal(jsondoc.New(10000))

func main() {
	jsondoc.Baseline("unmarshal-any", func() {
		for range 8 {
			var tree any
			if err := json.Unmarshal([]byte(input), &tree); err != nil {
				panic(err)
			}
		}
	})
	harness.Run(8, workload)
}

func workload(n int) string {
	total := 0
	for range n {
		var doc jsondoc.Document
		if err := json.Unmarshal([]byte(input), &doc); err != nil {
			panic(err)
		}
		total += jsondoc.Checksum(doc)
	}
	return strconv.Itoa(jsondoc.Units(input)) + " " + strconv.Itoa(total)
}
