#![deny(warnings)]

use std::env::args;
use std::process::exit;

fn main() {
    let status = args()
        .nth(1)
        .map(|s| i32::from_str_radix(&s, 10).expect("not a valid status"))
        .unwrap_or(0);
    exit(status);
}
