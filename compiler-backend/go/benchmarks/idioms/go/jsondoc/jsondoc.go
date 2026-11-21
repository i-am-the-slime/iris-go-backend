// Package jsondoc is the document of Bench.Idiom.Json.Document as Go structs
// for encoding/json.
package jsondoc

import (
	"encoding/json"
	"fmt"
	"os"
	"strconv"
	"time"
	"unicode/utf16"
)

type Document struct {
	Owner   string `json:"owner"`
	Version int    `json:"version"`
	Items   []Item `json:"items"`
}

type Item struct {
	ID    int      `json:"id"`
	Name  string   `json:"name"`
	Price float64  `json:"price"`
	Tags  []string `json:"tags"`
	Dims  Dims     `json:"dims"`
	Note  *string  `json:"note,omitempty"`
}

type Dims struct {
	W float64 `json:"w"`
	H float64 `json:"h"`
}

const alphabet = "abcdefghijklmnopqrstuvwxyz"

func New(size int) Document {
	items := make([]Item, size)
	for i := range items {
		tags := make([]string, i%4+1)
		for j := range tags {
			tags[j] = "t" + strconv.Itoa((i+j)%13)
		}
		var note *string
		if i%7 == 0 {
			text := "line\nbreak\t\"q\" café " + strconv.Itoa(i)
			note = &text
		}
		items[i] = Item{
			ID:    i,
			Name:  "item-" + strconv.Itoa(i) + "-" + alphabet[:i%17],
			Price: float64(i%1000) / 8,
			Tags:  tags,
			Dims:  Dims{W: float64(i%50) + 0.5, H: float64(i%30) * 2.25},
			Note:  note,
		}
	}
	return Document{Owner: "bench \"owner\" naïve", Version: 3, Items: items}
}

// Units is a string's length in UTF-16 code units, as PureScript counts it.
func Units(s string) int {
	n := 0
	for _, r := range s {
		n += utf16.RuneLen(r)
	}
	return n
}

func Checksum(doc Document) int {
	total := doc.Version
	for _, it := range doc.Items {
		total += it.ID + Units(it.Name) + int(it.Price*8) + len(it.Tags)
		for _, t := range it.Tags {
			total += Units(t)
		}
		total += int(it.Dims.W*2 + it.Dims.H*4)
		if it.Note != nil {
			total += Units(*it.Note)
		}
	}
	return total
}

func Marshal(doc Document) string {
	encoder := json.Marshal
	out, err := encoder(doc)
	if err != nil {
		panic(err)
	}
	return string(out)
}

// Baseline times one extra encoding/json workload five times and reports its
// best on stderr as `BASELINE name ms`, beside the harness's own BENCH line.
func Baseline(name string, work func()) {
	best := 0.0
	for r := range 5 {
		started := time.Now()
		work()
		elapsed := float64(time.Since(started).Nanoseconds()) / 1e6
		if r == 0 || elapsed < best {
			best = elapsed
		}
	}
	fmt.Fprintf(os.Stderr, "BASELINE %s %.3f\n", name, best)
}
