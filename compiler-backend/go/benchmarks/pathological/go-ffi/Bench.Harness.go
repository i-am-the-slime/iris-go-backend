// Clock, repetition count and CPU profile for the pathological benchmarks.
package Bench_Harness_ffi

import (
	"fmt"
	"os"
	"runtime/pprof"
	"strconv"
	"time"

	// The GC pacing every Markgraf host uses (GOGC=400 unless GOGC is set), so that the suite
	// measures generated code in the configuration it ships in.
	_ "github.com/i-am-the-slime/purs-backend-go/go-support/gctune"
)

var started time.Time

func StartClock(size int) func() int {
	return func() int {
		started = time.Now()
		return size
	}
}

func StopClock(_ string) func() float64 {
	return func() float64 { return float64(time.Since(started).Nanoseconds()) / 1e6 }
}

func RepetitionCount() int {
	configured, err := strconv.Atoi(os.Getenv("PATHO_REPETITIONS"))
	if err != nil || configured <= 0 {
		return 5
	}
	return configured
}

var profile *os.File

func StartProfile() {
	path := os.Getenv("PATHO_CPUPROFILE")
	if path == "" {
		return
	}
	file, err := os.Create(path)
	if err != nil {
		panic(err)
	}
	profile = file
	if err := pprof.StartCPUProfile(file); err != nil {
		panic(err)
	}
}

func StopProfile() {
	if profile == nil {
		return
	}
	pprof.StopCPUProfile()
	profile.Close()
	profile = nil
}

func LogTiming(best float64, first float64) func() {
	return func() { fmt.Fprintf(os.Stderr, "BENCH %.3f %.3f\n", best, first) }
}
