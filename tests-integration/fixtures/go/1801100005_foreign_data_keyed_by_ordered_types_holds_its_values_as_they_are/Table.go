package ffi

import (
	"cmp"
	"maps"
	"slices"
)

type Table[K cmp.Ordered, V any] = map[K]V

func Empty[K cmp.Ordered, V any]() map[K]V { return map[K]V{} }

func LookupImpl[K cmp.Ordered, V, M any](just func(V) M, nothing M, key K, entries map[K]V) M {
	if value, found := entries[key]; found {
		return just(value)
	}
	return nothing
}

func Insert[K cmp.Ordered, V any](key K, value V, entries map[K]V) { entries[key] = value }

func Values[K cmp.Ordered, V any](entries map[K]V) []V {
	sorted := make([]V, 0, len(entries))
	for _, key := range slices.Sorted(maps.Keys(entries)) {
		sorted = append(sorted, entries[key])
	}
	return sorted
}
