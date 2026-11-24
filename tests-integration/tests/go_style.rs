fn go_style(path: &std::path::Path) -> datatest_stable::Result<()> {
    tests_integration::fixtures::go_style(path)
}

datatest_stable::harness! {
    { test = go_style, root = "fixtures/go_style", pattern = r".*/Main\.purs$" },
}
