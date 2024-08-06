use std::{fs::File, io::Write, path::PathBuf};

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

    if cfg!(target_arch = "riscv64") {
        generate_riscv64_consts();
    }
}

fn generate_riscv64_consts() {
    println!("cargo:rerun-if-changed=build/get_riscv64_consts.c");

    let expanded = cc::Build::new().file("build/get_riscv64_consts.c").expand();
    let expanded = String::from_utf8(expanded).unwrap();

    let mut float_abi_double = false;
    let mut float_abi_soft = false;
    for line in expanded.lines() {
        match line.trim() {
            "CEE_SCAPE_FLOAT_ABI_DOUBLE" => float_abi_double = true,
            "CEE_SCAPE_FLOAT_ABI_SOFT" => float_abi_soft = true,
            _ => {}
        }
    }

    let out_dir: PathBuf = std::env::var("OUT_DIR")
        .expect("OUT_DIR env variable should be available")
        .into();
    println!("cargo::rustc-env=OUT_DIR={}", out_dir.display());

    let mut riscv64_consts_file = File::create(out_dir.join("riscv64_consts.rs"))
        .expect("unable to create riscv64_consts.rs");
    writeln!(
        riscv64_consts_file,
        "const FLOAT_ABI_DOUBLE: bool = {float_abi_double};\n\
        const FLOAT_ABI_SOFT: bool = {float_abi_soft};"
    )
    .expect("unable to write to riscv64_consts.rs");
    riscv64_consts_file
        .flush()
        .expect("unable to write to riscv64_consts.rs");
}
