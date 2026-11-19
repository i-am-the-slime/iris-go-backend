package harness

import (
	"fmt"
	"os"
	"runtime"
	"runtime/pprof"
	"strconv"
	"time"

	_ "github.com/i-am-the-slime/purs-backend-go/go-support/gctune"
)

func Run(size int, workload func(n int) string) {
	if configured, err := strconv.Atoi(os.Getenv("PATHO_SIZE")); err == nil && configured > 0 {
		size = configured
	}
	repetitions := 5
	if configured, err := strconv.Atoi(os.Getenv("PATHO_REPETITIONS")); err == nil && configured > 0 {
		repetitions = configured
	}
	var before runtime.MemStats
	if os.Getenv("PATHO_MEMSTATS") != "" {
		runtime.ReadMemStats(&before)
	}
	profile := startProfile()
	var timings []float64
	var results []string
	for range repetitions {
		started := time.Now()
		result := workload(size)
		timings = append(timings, float64(time.Since(started).Nanoseconds())/1e6)
		results = append(results, result)
	}
	if profile != nil {
		pprof.StopCPUProfile()
		profile.Close()
	}
	if os.Getenv("PATHO_MEMSTATS") != "" {
		var after runtime.MemStats
		runtime.ReadMemStats(&after)
		fmt.Fprintf(os.Stderr, "ALLOCS %d %d\n", after.Mallocs-before.Mallocs, after.TotalAlloc-before.TotalAlloc)
	}
	report(timings, results)
}

func startProfile() *os.File {
	path := os.Getenv("PATHO_CPUPROFILE")
	if path == "" {
		return nil
	}
	file, err := os.Create(path)
	if err != nil {
		panic(err)
	}
	if err := pprof.StartCPUProfile(file); err != nil {
		panic(err)
	}
	return file
}

func report(timings []float64, results []string) {
	stable := true
	for _, result := range results {
		stable = stable && result == results[0]
	}
	if stable {
		fmt.Println(results[0])
	} else {
		fmt.Printf("UNSTABLE %v\n", results)
	}
	best := timings[0]
	for _, timing := range timings {
		best = min(best, timing)
	}
	fmt.Fprintf(os.Stderr, "BENCH %.3f %.3f\n", best, timings[0])
}

func Xorshift(seed int32) int32 {
	a := seed ^ (seed << 13)
	b := a ^ int32(uint32(a)>>17)
	return b ^ (b << 5)
}

func PseudoRandomArray(count int) []int32 {
	values := make([]int32, count)
	for i := range values {
		values[i] = Xorshift(int32(i + 1))
	}
	return values
}
