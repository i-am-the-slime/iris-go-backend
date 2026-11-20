package ffi

type Output struct {
	Stdout   string
	Stderr   string
	ExitCode int32
}

func Run(program string) func() Output {
	return func() Output { return Output{Stdout: program} }
}

func RunAll(programs []string) func() []Output {
	return func() []Output {
		outputs := make([]Output, len(programs))
		for index, program := range programs {
			outputs[index] = Output{Stdout: program}
		}
		return outputs
	}
}

func Describe(output Output) string { return output.Stdout }
