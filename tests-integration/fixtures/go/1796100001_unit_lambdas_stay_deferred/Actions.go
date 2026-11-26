package ffi

func RunWhenAsked(action func() int) int {
	return action()
}
