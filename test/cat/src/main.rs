#![deny(warnings)]

use std::io::{stdin, stdout, copy};

fn main() {
    let stdin_handle = stdin();
    let stdout_handle = stdout();
    copy(&mut stdin_handle.lock(), &mut stdout_handle.lock()).unwrap();
}
