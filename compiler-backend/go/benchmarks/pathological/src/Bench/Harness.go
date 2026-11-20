// Clock, repetition count and CPU profile for the pathological benchmarks.
package Bench_Harness_ffi

import (
	"fmt"
	"os"
	"runtime"
	"runtime/pprof"
	"strconv"
	"time"

	// The GC pacing every Markgraf host uses (GOGC=400 unless GOGC is set), so that the suite
	// measures generated code in the configuration it ships in.
	_ "github.com/i-am-the-slime/iris-go/gctune"
)

var started time.Time

// PATHO_SIZE replaces the benchmark's size, so that scripts/robust/scaling.sh can time it at n, 2n
// and 4n.
func StartClock(size int32) int32 {
	if configured, ok := positive("PATHO_SIZE"); ok {
		size = configured
	}
	started = time.Now()
	return size
}

func StopClock(_ string) float64 { return float64(time.Since(started).Nanoseconds()) / 1e6 }

func RepetitionCount() int32 {
	if configured, ok := positive("PATHO_REPETITIONS"); ok {
		return configured
	}
	return 5
}

// positive reads a positive Int from the environment variable. A value outside Int's range is as
// invalid as any other non-number.
func positive(variable string) (int32, bool) {
	configured, err := strconv.ParseInt(os.Getenv(variable), 10, 32)
	if err != nil || configured <= 0 {
		return 0, false
	}
	return int32(configured), true
}

var profile *os.File

// With PATHO_MEMSTATS set, StopProfile reports the heap allocations made by every repetition
// together, as `ALLOCS objects bytes` on stderr.
var allocated runtime.MemStats

func StartProfile() {
	if os.Getenv("PATHO_MEMSTATS") != "" {
		runtime.ReadMemStats(&allocated)
	}
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
	if os.Getenv("PATHO_MEMSTATS") != "" {
		var now runtime.MemStats
		runtime.ReadMemStats(&now)
		fmt.Fprintf(os.Stderr, "ALLOCS %d %d\n", now.Mallocs-allocated.Mallocs, now.TotalAlloc-allocated.TotalAlloc)
	}
	if profile == nil {
		return
	}
	pprof.StopCPUProfile()
	profile.Close()
	profile = nil
}

func LogTiming(best float64, first float64) {
	fmt.Fprintf(os.Stderr, "BENCH %.3f %.3f\n", best, first)
}
