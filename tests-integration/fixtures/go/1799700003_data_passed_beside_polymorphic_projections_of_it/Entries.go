package ffi

import (
	"strconv"
	"strings"
)

func JoinEntriesImpl[F any](first func(F) any, second func(F) any, entries []F) string {
	joined := make([]string, len(entries))
	for i, entry := range entries {
		joined[i] = first(entry).(string) + "=" + strconv.Itoa(int(second(entry).(int32)))
	}
	return strings.Join(joined, ",")
}
