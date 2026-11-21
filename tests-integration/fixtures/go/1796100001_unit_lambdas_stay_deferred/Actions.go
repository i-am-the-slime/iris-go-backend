package ffi

func RunWhenAsked(action func() int32) int32 {
	return action()
}
