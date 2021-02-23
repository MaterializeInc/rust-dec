// Copyright Materialize, Inc. All rights reserved.
//
// This software is made available under the terms of the
// ICU license -- ICU 1.8.1 and later.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let declitend = if cfg!(target_endian = "little") {
        "1"
    } else {
        "0"
    };
    cc::Build::new()
        .define("DECLITEND", Some(declitend))
        .file("decnumber/decimal128.c")
        .file("decnumber/decimal64.c")
        .file("decnumber/decimal32.c")
        .file("decnumber/decContext.c")
        .file("decnumber/decNumber.c")
        .file("decnumber/decSingle.c")
        .file("decnumber/decDouble.c")
        .file("decnumber/decQuad.c")
        .file("decnumber/decPacked.c")
        .out_dir(out_dir.join("lib"))
        .compile("decnumber");

    let include_dir = out_dir.join("include");
    fs::create_dir_all(&include_dir).unwrap_or_else(|e| {
        panic!(
            "failed to create include directory {}: {}",
            include_dir.display(),
            e
        )
    });
    for header in &[
        "decimal128.h",
        "decimal64.h",
        "decimal32.h",
        "decContext.h",
        "decNumber.h",
        "decSingle.h",
        "decDouble.h",
        "decQuad.h",
        "decPacked.h",
        "decDPD.h",
        "decNumberLocal.h",
    ] {
        let src = Path::new("decnumber").join(header);
        let dst = out_dir.join("include").join(header);
        fs::copy(&src, &dst).unwrap_or_else(|e| {
            panic!(
                "failed to copy {} to include directory: {}",
                src.display(),
                e
            )
        });
    }

    println!("cargo:root={}", out_dir.display());
}
