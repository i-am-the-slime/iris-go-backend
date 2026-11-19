package main

import (
	"strconv"

	"idioms.example/hand/harness"
)

func main() { harness.Run(1000000, workload) }

func workload(n int) string {
	rotated := rot13(build(n))
	return strconv.Itoa(len(rotated)) + " " + strconv.Itoa(vowels(rotated)) + " " + rotated[:16]
}

func build(n int) string {
	letters := make([]byte, n)
	for i := range letters {
		letters[i] = byte(97 + i%26)
	}
	return string(letters)
}

func rot13(text string) string {
	rotated := make([]byte, len(text))
	for i := 0; i < len(text); i++ {
		c := text[i]
		if c >= 'a' && c <= 'z' {
			c = byte(97 + (int(c)-97+13)%26)
		}
		rotated[i] = c
	}
	return string(rotated)
}

func vowels(text string) int {
	count := 0
	for i := 0; i < len(text); i++ {
		switch text[i] {
		case 'a', 'e', 'i', 'o', 'u':
			count++
		}
	}
	return count
}
