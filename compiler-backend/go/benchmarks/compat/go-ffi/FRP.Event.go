// hyrule's FRP.Event foreign imports (src/FRP/Event.js in hyrule 2.4.0), ported for the
// compatibility corpus. `ObjHack a` is a PureScript `data` type without constructors, which the
// backend erases to `any`, so the subscriber table arrives here as `any`.
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

// subscribers mirrors the JavaScript object `{ r, q, m }`: whether a push is running, the pushes
// queued behind it, and a stack of key-to-subscriber maps, one per nesting level of the running
// push. JavaScript iterates integer keys in ascending order, so every iteration sorts them.
type subscribers struct {
	running bool
	queue   []func()
	levels  []map[int]any
}

func ObjHack() any {
	return &subscribers{levels: []map[int]any{{}}}
}

func InsertObjHack[A any](key int, value A, table any) func() {
	return func() {
		object := table.(*subscribers)
		object.levels[len(object.levels)-1][key] = value
	}
}

// DeleteObjHack removes the key from the first level only: JavaScript's `delete` reports success
// whether or not the key was present, so the loop in Event.js stops after the first map.
func DeleteObjHack(key int, table any) func() {
	return func() {
		object := table.(*subscribers)
		if len(object.levels) > 0 {
			delete(object.levels[0], key)
		}
	}
}

func FastForeachOhE[A any](table any, f func(A) func()) func() {
	return func() { foreachSubscriber(table.(*subscribers), f) }
}

func foreachSubscriber[A any](object *subscribers, f func(A) func()) {
	if object.running {
		object.queue = append(object.queue, func() { foreachSubscriber(object, f) })
		return
	}
	object.running = true
	merged := map[int]any{}
	var run func(level int)
	run = func(level int) {
		object.levels = append(object.levels, map[int]any{})
		current := object.levels[level]
		for _, key := range sortedKeys(current) {
			value := current[key]
			f(value.(A))()
			if len(object.levels[level+1]) > 0 {
				run(level + 1)
			}
			object.levels[level+1] = map[int]any{}
			object.levels = object.levels[:level+2]
			merged[key] = value
		}
	}
	run(0)
	object.levels = []map[int]any{merged}
	object.running = false
	for len(object.queue) > 0 {
		next := object.queue[0]
		object.queue = object.queue[1:]
		next()
	}
}

func sortedKeys(entries map[int]any) []int {
	keys := make([]int, 0, len(entries))
	for key := range entries {
		keys = append(keys, key)
	}
	sort.Ints(keys)
	return keys
}
