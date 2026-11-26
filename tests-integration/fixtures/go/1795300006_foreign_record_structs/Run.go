package ffi

type Output struct {
	Stdout   string
	Stderr   string
	ExitCode int
}

func Run(program string) Output { return Output{Stdout: program} }

func RunAll(programs []string) []Output {
	outputs := make([]Output, len(programs))
	for index, program := range programs {
		outputs[index] = Output{Stdout: program}
	}
	return outputs
}

func Describe(output Output) string { return output.Stdout }
