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
use std::error::Error;
use std::path::PathBuf;
use std::process;

use dectest::ast;
use dectest::backend::{Decimal128Backend, Decimal32Backend, Decimal64Backend, DecimalBackend};
use dectest::parse;
use dectest::run::{self, Outcome, Report};

fn main() {
    if let Err(e) = run() {
        eprintln!("error: {}", e);
        process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut paths = vec![];
    let mut verbose = false;
    let mut backend = BackendSpec::Decimal128;
    let mut args = env::args().into_iter().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-v" => verbose = true,
            "-b" => match args.next().as_deref() {
                None => return Err("-b flag requires a value".into()),
                Some("decimal") => backend = BackendSpec::Decimal,
                Some("decimal32") => backend = BackendSpec::Decimal32,
                Some("decimal64") => backend = BackendSpec::Decimal64,
                Some("decimal128") => backend = BackendSpec::Decimal128,
                Some(b) => return Err(format!("unknown backend \"{}\"", b).into()),
            },
            _ => paths.push(PathBuf::from(arg)),
        }
    }
    if paths.is_empty() {
        return Err("usage: dectest [-v] [-b BACKEND] <FILE>...".into());
    }

    let mut reporter = ConsoleReporter::new(verbose);

    for path in paths {
        let file = parse::parse_file(&path)?;
        match backend {
            BackendSpec::Decimal => run::run_file::<DecimalBackend, _>(&mut reporter, &file)?,
            BackendSpec::Decimal32 => run::run_file::<Decimal32Backend, _>(&mut reporter, &file)?,
            BackendSpec::Decimal64 => run::run_file::<Decimal64Backend, _>(&mut reporter, &file)?,
            BackendSpec::Decimal128 => run::run_file::<Decimal128Backend, _>(&mut reporter, &file)?,
        }
    }

    println!("PASS {}", reporter.passes);
    println!("FAIL {}", reporter.failures);
    println!("SKIP {}", reporter.skips);

    if reporter.failures > 0 {
        process::exit(1)
    }
    Ok(())
}

enum BackendSpec {
    Decimal,
    Decimal32,
    Decimal64,
    Decimal128,
}

struct ConsoleReporter {
    failures: usize,
    passes: usize,
    skips: usize,
    verbose: bool,
}

impl ConsoleReporter {
    fn new(verbose: bool) -> ConsoleReporter {
        ConsoleReporter {
            failures: 0,
            passes: 0,
            skips: 0,
            verbose,
        }
    }
}

impl Report for ConsoleReporter {
    fn start_file(&mut self, file: &ast::File) {
        println!("==> {}", file.path.display())
    }

    fn finish_file(&mut self) {}

    fn start_test(&mut self, test: &ast::Test) {
        if self.verbose {
            print!("{} {} -> {}", test.id, test.operation, test.result);
            if !test.conditions.is_empty() {
                let conditions: Vec<_> = test.conditions.iter().map(|c| c.to_string()).collect();
                print!(" ({})", conditions.join(", "));
            }
            println!();
        } else {
            print!("{} ", test.id);
        }
    }

    fn finish_test(&mut self, outcome: Outcome) {
        match outcome {
            Outcome::Passed => self.passes += 1,
            Outcome::Failed { .. } => self.failures += 1,
            Outcome::Skipped => self.skips += 1,
        }
        match outcome {
            Outcome::Passed => println!("PASS"),
            Outcome::Failed { cause } => println!("FAIL: {}", cause),
            Outcome::Skipped => println!("SKIP"),
        }
        if self.verbose {
            println!()
        }
    }
}
