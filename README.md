# duct.rs [![Travis build](https://travis-ci.org/oconnor663/duct.rs.svg?branch=master)](https://travis-ci.org/oconnor663/duct.rs) [![AppVeyor build](https://ci.appveyor.com/api/projects/status/0ecgamtb43j8o8ig/branch/master?svg=true)](https://ci.appveyor.com/project/oconnor663/duct-rs/branch/master) [![crates.io](https://img.shields.io/crates/v/duct.svg)](https://crates.io/crates/duct) [![docs.rs](https://docs.rs/duct/badge.svg)](https://docs.rs/duct)

A cross-platform library for running child processes and building
pipelines.

`duct` wants to make shelling out in Rust as easy and flexible as it is in
Bash. It takes care of [gotchas and
inconsistencies](https://github.com/oconnor663/duct.py/blob/master/spec.md)
in the way different platforms shell out. And it's a cross-language library;
the [original implementation](https://github.com/oconnor663/duct.py) is in
Python, with an identical API.

- [Docs](https://docs.rs/duct)
- [Crate](https://crates.io/crates/duct)
- [Repo](https://github.com/oconnor663/duct.rs)

## Changelog

- Version 0.9 removed the `sh` function. It now lives in its own crate,
`duct_sh`.

## Example

`duct` tries to be as concise as possible, so that you don't wish you were
back writing shell scripts. At the same time, it's explicit about what
happens to output, and strict about error codes in child processes.

```rust,no_run
#[macro_use]
extern crate duct;

use duct::cmd;

fn main() {
    // Read the name of the current git branch. If git exits with an error
    // code here (because we're not in a git repo, for example), `read` will
    // return an error too.
    let current_branch = cmd!("git", "symbolic-ref", "--short", "HEAD").read().unwrap();

    // Log the current branch, with git taking over the terminal as usual.
    // The `cmd` function works just like the `cmd!` macro, but it takes a
    // collection instead of a variable list of arguments.
    let args = &["log", &current_branch];
    cmd("git", args).run().unwrap();

    // More complicated expressions become trees. Here's a pipeline with two
    // child processes on the left, just because we can. In Bash this would
    // be: stdout=$((echo -n part one "" && echo part two) | sed s/p/sm/g)
    let part_one = &["-n", "part", "one", ""];
    let stdout = cmd("echo", part_one)
        .then(cmd!("echo", "part", "two"))
        .pipe(cmd!("sed", "s/p/sm/g"))
        .read()
        .unwrap();
    assert_eq!("smart one smart two", stdout);
}
```

`duct` uses [`os_pipe`](https://github.com/oconnor663/os_pipe.rs)
internally, and the docs for that one include a [big
example](https://docs.rs/os_pipe#example) that takes a dozen lines of code
to read both stdout and stderr from a child process. `duct` can do that in
one (moderately long) line:

```rust
# #[macro_use] extern crate duct;
# fn main() {
# if cfg!(not(windows)) {
let output = cmd!("sh", "-c", "echo foo && echo bar 2>&1").stderr_to_stdout().read().unwrap();

assert!(output.split_whitespace().eq(vec!["foo", "bar"]));
# }
# }
```
