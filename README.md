# duct.rs [![Travis build](https://travis-ci.org/oconnor663/duct.rs.svg?branch=master)](https://travis-ci.org/oconnor663/duct.rs) [![AppVeyor build](https://ci.appveyor.com/api/projects/status/89o6o64nxfl80s78/branch/master?svg=true)](https://ci.appveyor.com/project/oconnor663/os-pipe-rs/branch/master) [![crates.io](https://img.shields.io/crates/v/duct.svg)](https://crates.io/crates/duct) [![docs.rs](https://docs.rs/duct/badge.svg)](https://docs.rs/duct)

A cross-platform library for running child processes and building
pipelines.

`duct` wants to make shelling out in Rust as easy and flexible as it
is in Bash. It also takes care of [tricky
inconsistencies](https://github.com/oconnor663/duct.py/blob/master/spec.md#consistent-behavior-for-dir)
in the way different platforms shell out. And it's a cross-language
library; the [original
implementation](https://github.com/oconnor663/duct.py) is in Python,
with an identical API.

- [Docs](https://docs.rs/duct)
- [Crate](https://crates.io/crates/duct)
- [Repo](https://github.com/oconnor663/duct.rs)

## Example

`duct` uses [`os_pipe`](https://github.com/oconnor663/os_pipe.rs)
internally, and the docs for that one include a [big
example](https://docs.rs/os_pipe#example) that uses more than a
dozen lines of code to read both stdout and stderr from a child
process. `duct` can do that in one line:

```rust
use duct::sh;

let output = sh("echo foo && echo bar >&2").stderr_to_stdout().read().unwrap();

assert!(output.split_whitespace().eq(vec!["foo", "bar"]));
```
