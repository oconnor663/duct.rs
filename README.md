# duct.rs [![Travis build](https://travis-ci.org/oconnor663/duct.rs.svg?branch=master)](https://travis-ci.org/oconnor663/duct.rs) [![AppVeyor build](https://ci.appveyor.com/api/projects/status/w3g0fplnx234bxji/branch/master?svg=true)](https://ci.appveyor.com/project/oconnor663/duct-rs/branch/master) [![crates.io](https://img.shields.io/crates/v/duct.svg)](https://crates.io/crates/duct) [![docs.rs](https://docs.rs/duct/badge.svg)](https://docs.rs/duct)

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

- Version 0.12 added support for trailing commas to `cmd!`.
- Version 0.11 introduced the `before_spawn` method.
- Version 0.10 changed how environment variable casing is handled on Windows.
  See the docs for `env_remove`.
- Version 0.9 removed the `sh` function. It now lives in its own crate, `duct_sh`.

## Example

`duct` tries to be as concise as possible, so that you don't wish you were
back writing shell scripts. At the same time, it's explicit about what
happens to output, and strict about error codes in child processes.

```rust
// Read the name of the current git branch. If git exits with an error
// code here (because we're not in a git repo, for example), `read` will
// return an error too.
let current_branch = cmd!("git", "symbolic-ref", "--short", "HEAD").read()?;

// Log the current branch, with git taking over the terminal as usual.
// The `cmd` function works just like the `cmd!` macro, but it takes a
// collection instead of a variable list of arguments.
let args = &["log", &current_branch];
cmd("git", args).run()?;

// Log again, but this time read the output from a pipe of our own. We
// use the os_pipe crate to create the pipe, but any type implementing
// IntoRawFd works here, including File.
let (pipe_reader, pipe_writer) = os_pipe::pipe()?;
let child = cmd!("git", "log", "--oneline").stdout_handle(pipe_writer).start()?;
for line in BufReader::new(pipe_reader).lines() {
    assert!(!line?.contains("heck"), "profanity filter triggered");
}
```

`duct` uses [`os_pipe`](https://github.com/oconnor663/os_pipe.rs)
internally, and the docs for that one include a [big
example](https://docs.rs/os_pipe#example) that takes a dozen lines of code
to read both stdout and stderr from a child process. `duct` can do that in
one (moderately long) line:

```rust
let output = cmd!("sh", "-c", "echo foo && echo bar 2>&1").stderr_to_stdout().read().unwrap();

assert!(output.split_whitespace().eq(vec!["foo", "bar"]));
```
