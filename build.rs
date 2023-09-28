fn main() {
    if std::env::var("CARGO_FEATURE_TEST_C_INTEGRATION")
        .ok()
        .is_some()
    {
        cc::Build::new()
            .file("src/test_c_integration.c")
            .compile("test_c_integration");
    } else {
        panic!("did not see it");
    }

    if std::env::var("CARGO_FEATURE_USE_C_TO_INTERFACE_WITH_SETJMP")
        .ok()
        .is_some()
    {
        cc::Build::new()
            .file("src/interop_via_c.c")
            .compile("interop_via_c");
    } else {
    }
}
