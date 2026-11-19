package main

import (
	"math"
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(200000, workload) }

type body struct {
	x, y, z, vx, vy, vz, mass float64
}

func workload(steps int) string {
	bodies := initial()
	for range steps {
		advance(0.01, bodies)
	}
	return strconv.FormatFloat(energy(bodies), 'f', 9, 64)
}

func advance(dt float64, bodies []body) {
	for i := range bodies {
		for j := range bodies {
			if i == j {
				continue
			}
			dx := bodies[j].x - bodies[i].x
			dy := bodies[j].y - bodies[i].y
			dz := bodies[j].z - bodies[i].z
			distanceSquared := dx*dx + dy*dy + dz*dz
			magnitude := dt / (distanceSquared * math.Sqrt(distanceSquared))
			bodies[i].vx += dx * bodies[j].mass * magnitude
			bodies[i].vy += dy * bodies[j].mass * magnitude
			bodies[i].vz += dz * bodies[j].mass * magnitude
		}
	}
	for i := range bodies {
		bodies[i].x += dt * bodies[i].vx
		bodies[i].y += dt * bodies[i].vy
		bodies[i].z += dt * bodies[i].vz
	}
}

func energy(bodies []body) float64 {
	total := 0.0
	for i, b := range bodies {
		total += 0.5 * b.mass * (b.vx*b.vx + b.vy*b.vy + b.vz*b.vz)
		for j := i + 1; j < len(bodies); j++ {
			dx := b.x - bodies[j].x
			dy := b.y - bodies[j].y
			dz := b.z - bodies[j].z
			total -= b.mass * bodies[j].mass / math.Sqrt(dx*dx+dy*dy+dz*dz)
		}
	}
	return total
}

func initial() []body {
	return []body{
		{0, 0, 0, 0, 0, 0, 39.47841760435743},
		{4.84143144246472090, -1.16032004402742839, -0.103622044471123109, 0.606326392995832, 2.81198684491626, -0.02521836165988763, 0.03769367487038949},
		{8.34336671824457987, 4.12479856412430479, -0.403523417114321381, -1.0107743461787924, 1.8256623712304119, 0.008415761376584154, 0.011286326131968767},
		{12.8943695621391310, -15.1111514016986312, -0.223307578892655734, 1.0827910064415354, 0.8687130181696082, -0.010832637401363636, 0.0017237240570597112},
		{15.3796971148509165, -25.9193146099879641, 0.179258772950371181, 0.979090732243898, 0.5946989986476762, -0.034755955504078104, 0.0020336868699246304},
	}
}
