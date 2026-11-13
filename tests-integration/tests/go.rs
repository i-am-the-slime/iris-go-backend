fn go(path: &std::path::Path) -> datatest_stable::Result<()> {
    tests_integration::fixtures::go(path)
}

datatest_stable::harness! {
    { test = go, root = "fixtures/go", pattern = r".*/Main\.purs$" },
}
