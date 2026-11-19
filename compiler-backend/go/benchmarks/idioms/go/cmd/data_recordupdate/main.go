package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(10000000, workload) }

type particle struct {
	position int32
	velocity int32
	bounces  int32
}

func workload(n int) string {
	final := particle{position: 0, velocity: 7, bounces: 0}
	for i := 1; i <= n; i++ {
		final = step(final)
	}
	return strconv.Itoa(int(final.position)) + " " + strconv.Itoa(int(final.velocity)) + " " + strconv.Itoa(int(final.bounces))
}

func step(p particle) particle {
	p.position += p.velocity
	if p.position > 1000 || p.position < -1000 {
		p.velocity = -p.velocity
		p.bounces++
	}
	return p
}
