# duct_sh

The `sh` function was originally included in the `duct` library itself.
Because of safety concerns, we decided to split that function into `sh`
(taking only static strings) and `sh_dangerous` (taking any string). That in
turn raised a portability problem: duct is a
[multi-language](https://github.com/oconnor663/duct.py) library, and most
languages can't distinguish string lifetimes the way that Rust can. As an
experiment, we're splitting these functions into their own crate, with the
intention of keeping them Rust-only.

I don't know if we'll keep this arrangement, but here are some other
points in favor:

- Simple `sh` commands are nice when you first write them, but it feels
  annoying to rewrite them as `cmd!` once you need to introduce a variable
  somewhere. That annoyance is pressure to do something evil.
- Legitimate use cases for `sh_dangerous` in small scripts are rare. The
  common use case is something like a build tool, where the user is expected
  to run arbitrary shell commands through the tool. Importing an extra crate
  (or just copying the whole function) is less of a big deal in the source
  code of a build tool than it is in a small script.
- Many languages have standard library support for launching shell commands.
  Rust doesn't, and so `duct_sh` is more valuable in Rust than it would be
  in say Python.
