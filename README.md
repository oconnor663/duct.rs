# duct.rs [![Build Status](https://travis-ci.org/oconnor663/duct.rs.svg?branch=master)](https://travis-ci.org/oconnor663/duct.rs)

A Rust port of [duct.py](https://github.com/oconnor663/duct.py). Here's
the [crates.io package](https://crates.io/crates/duct). A work in
progress.

```rust
#[macro_use(cmd)]
extern crate duct;

use duct::{sh, OutputRedirect};

fn main() {
    // Read the name of the current git branch.
    let current_branch = sh("git symbolic-ref --short HEAD").read().unwrap();
    assert_eq!(current_branch, "master");

    // Log the current branch, with git taking over the terminal as usual.
    cmd!("git", "log", current_branch).run().unwrap();

    // Gratuitously pipe a bunch of commands together.
    let result = sh("echo -n The future")
        .then(sh("echo $HORRIFYING_ERROR >&2"))
        .env("HORRIFYING_ERROR", "was then!")
        .stderr(OutputRedirect::Stdout)
        .pipe(cmd!("sed", "s/was then/ is now/"))
        .stdout(OutputRedirect::Capture)
        .run()
        .unwrap();
    assert_eq!(result.status, 0);
    assert_eq!(result.stdout, b"The future is now!\n");
    assert_eq!(result.stderr, b"");
}
```
