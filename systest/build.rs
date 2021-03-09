// Copyright Materialize, Inc. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE file at the
// root of this repository, or online at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::env;
use std::path::PathBuf;

fn main() {
    let root = PathBuf::from(env::var_os("DEP_DECNUMBER_ROOT").unwrap());

    ctest::TestGenerator::new()
        .include(".")
        .include(root.join("include"))
        .header("decimal128.h")
        .header("decimal64.h")
        .header("decimal32.h")
        .header("decContext.h")
        .header("decNumber.h")
        .header("decSingle.h")
        .header("decDouble.h")
        .header("decQuad.h")
        .header("decPacked.h")
        .header("decNumberLocal.h")
        .header("extra.h")
        .type_name(|ty, _is_struct, _is_union| match ty {
            "rounding" => "enum rounding".into(),
            "decClass" => "enum decClass".into(),
            _ => ty.to_string(),
        })
        .generate("../decnumber-sys/src/lib.rs", "all.rs");
}
