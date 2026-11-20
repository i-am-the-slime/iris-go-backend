package Shapes_ffi

import "github.com/i-am-the-slime/iris-go/direct"

func Measure(name string) *[]any {
	shapes := []any{direct.ForeignRecord([]string{"kind", "size"}, []any{name, int32(4)})}
	return &shapes
}

func Describe(shape any) string {
	return direct.ForeignField(shape, "name").(string)
}
