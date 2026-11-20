package ffi

import "time"

func Now() float64 { return float64(time.Now().UnixMilli()) }
