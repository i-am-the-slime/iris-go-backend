// The Go build's counterpart of markgraf's cli/native/main.rs: the host
// configuration for Tauri.Native, with the same bundled fonts under the same
// families, weights and styles. Copied next to the generated main.go together
// with the fonts directory.
package main

import (
	_ "embed"

	"github.com/i-am-the-slime/purs-backend-go/go-support/tauri"
)

var (
	//go:embed fonts/Ilisarniq-Demi.otf
	ilisarniqDemi []byte
	//go:embed fonts/VictorMono-Medium.ttf
	victorMonoMedium []byte
	//go:embed fonts/VictorMono-Bold.ttf
	victorMonoBold []byte
	//go:embed fonts/VictorMono-MediumItalic.ttf
	victorMonoMediumItalic []byte
	//go:embed fonts/VictorMono-BoldItalic.ttf
	victorMonoBoldItalic []byte
	//go:embed fonts/Ilisarniq-Italic.otf
	ilisarniqItalic []byte
)

// version is set with -ldflags "-X main.version=…", like MARKGRAF_VERSION.
var version = "dev"

func init() {
	tauri.Configure(tauri.Config{
		Version:     version,
		Application: "markgraf-editor",
		Fonts: []tauri.FontAsset{
			{Family: "Ilisarniq", Data: ilisarniqDemi, Weight: 500},
			{Family: "Victor Mono", Data: victorMonoMedium, Weight: 500},
			{Family: "Victor Mono", Data: victorMonoBold, Weight: 700},
			{Family: "Victor Mono", Data: victorMonoMediumItalic, Weight: 500, Italic: true},
			{Family: "Victor Mono", Data: victorMonoBoldItalic, Weight: 700, Italic: true},
			{Family: "Ilisarniq-Italic", Data: ilisarniqItalic, Weight: 400, Italic: true},
		},
	})
}
