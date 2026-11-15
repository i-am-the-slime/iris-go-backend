// hyrule's FRP.Event foreign imports (src/FRP/Event.js in hyrule 2.4.0), ported for the
// compatibility corpus. `ObjHack a`, a PureScript `data` type without constructors that only these
// foreigns build and read, is the named type ObjHackType this file declares (`objHack` takes the
// name ObjHack).
package FRP_Event_ffi

import "sort"

func FastForeachThunk(actions []func()) func() {
	return func() {
		for _, action := range actions {
			action()
		}
	}
}

func FastForeachE[A any](values []A, f func(A) func()) func() {
	return func() {
		for _, value := range values {
			f(value)()
		}
	}
}

// ObjHackType is hyrule's `ObjHack a`, the JavaScript object `{ r, q, m }`: whether a push is
// running, the pushes queued behind it, and a stack of key-to-subscriber maps, one per nesting
// level of the running push. JavaScript iterates integer keys in ascending order, so every
// iteration sorts them.
type ObjHackType[A any] struct{ table *subscribers[A] }

type subscribers[A any] struct {
	running bool
	queue   []func()
	levels  []map[int]A
}

func ObjHack[A any]() ObjHackType[A] {
	return ObjHackType[A]{&subscribers[A]{levels: []map[int]A{{}}}}
}

func InsertObjHack[A any](key int, value A, table ObjHackType[A]) func() {
	return func() {
		object := table.table
		object.levels[len(object.levels)-1][key] = value
	}
}

// DeleteObjHack removes the key from the first level only: JavaScript's `delete` reports success
// whether or not the key was present, so the loop in Event.js stops after the first map.
func DeleteObjHack[A any](key int, table ObjHackType[A]) func() {
	return func() {
		object := table.table
		if len(object.levels) > 0 {
			delete(object.levels[0], key)
		}
	}
}

func FastForeachOhE[A any](table ObjHackType[A], f func(A) func()) func() {
	return func() { foreachSubscriber(table.table, f) }
}

func foreachSubscriber[A any](object *subscribers[A], f func(A) func()) {
	if object.running {
		object.queue = append(object.queue, func() { foreachSubscriber(object, f) })
		return
	}
	object.running = true
	merged := map[int]A{}
	var run func(level int)
	run = func(level int) {
		object.levels = append(object.levels, map[int]A{})
		for _, entry := range sortedEntries(object.levels[level]) {
			key, value := entry.key, entry.value
			f(value)()
			if len(object.levels[level+1]) > 0 {
				run(level + 1)
			}
			object.levels[level+1] = map[int]A{}
			object.levels = object.levels[:level+2]
			merged[key] = value
		}
	}
	run(0)
	object.levels = []map[int]A{merged}
	object.running = false
	for len(object.queue) > 0 {
		next := object.queue[0]
		object.queue = object.queue[1:]
		next()
	}
}

// entry is one key-subscriber pair of a level, taken before its subscribers run: like
// `Object.entries` in Event.js, a subscriber removed by an earlier one in the same push still runs.
type entry[A any] struct {
	key   int
	value A
}

func sortedEntries[A any](level map[int]A) []entry[A] {
	entries := make([]entry[A], 0, len(level))
	for key, value := range level {
		entries = append(entries, entry[A]{key, value})
	}
	sort.Slice(entries, func(i, j int) bool { return entries[i].key < entries[j].key })
	return entries
}
