package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(5000000, workload) }

type kind uint8

const (
	circle kind = iota
	square
	rectangle
)

type shape struct {
	kind kind
	a    int
	b    int
}

func workload(n int) string {
	sides := make([]int, 64)
	for i := range sides {
		sides[i] = int(i + 1)
	}
	var total int
	for i := int(1); i <= int(n); i++ {
		total += area(makeShape(sides, i))
	}
	return strconv.Itoa(int(total))
}

func makeShape(sides []int, i int) shape {
	switch i % 3 {
	case 0:
		return shape{kind: circle, a: i & 15}
	case 1:
		side := int(1)
		if index := int(i & 63); index < len(sides) {
			side = sides[index]
		}
		return shape{kind: square, a: side}
	default:
		return shape{kind: rectangle, a: i & 15, b: (i >> 4) & 15}
	}
}

func area(s shape) int {
	switch s.kind {
	case circle:
		return 3 * s.a * s.a
	case square:
		return s.a * s.a
	default:
		return s.a * s.b
	}
}
