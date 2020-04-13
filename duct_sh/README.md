# duct_sh [![crates.io](https://img.shields.io/crates/v/duct_sh.svg)](https://crates.io/crates/duct_sh) [![docs.rs](https://docs.rs/duct_sh/badge.svg)](https://docs.rs/duct_sh)

A convenience wrapper around the `duct` crate for building commands out of
shell strings. Duct normally executes commands directly, without going
through a shell at all. This is preferable where possile, because it avoids
tricky whitespace issues and shell injection vulnerabilities. However,
sometimes you need access to more esoteric shell features (e.g. shell
builtins like `source` and `exec`, or process substitution with `<()`), and
other times you're just stuck with a string of shell code that you have to
run somehow.

In these situations, `duct_sh` is a "cross-platform" way to run shell
commands, in combination with all the usual features of Duct.
"Cross-platform" is in scare quotes, however, because shell code is
necessarily platform-specific. The typical Bourne-like shells on Unix and
the cmd.exe shell on Windows systems do have a lot in common, including the
`|` and `>` operators, but they diverge very quickly when you start to look
at the details. For that reason, seriously cross-platform programs should
avoid shell code as much as possible.

## Example

```rust
// Execute a static string of shell code.
let output = duct_sh::sh("echo $MSG | sed s/i/a/").env("MSG", "hi").read()?;
assert_eq!(output, "ha");

// Execute a dynamic string of shell code. Note that this requires the
// "sh_dangerous" function. See the Security section below.
let arg = "hi";
let command = format!("echo {} | sed s/i/a/", arg);
let output = duct_sh::sh_dangerous(&command).read()?;
assert_eq!(output, "ha");
```

## Security

The `sh` function is restricted to static strings. The `sh_dangerous`
function does exactly the same thing, but it accepts dynamic strings. The
scary name is because of security issues related to shell injection.
Consider this innocent-looking function:

```rust
fn echo_string(s: &str) {
    duct_sh::sh_dangerous(format!("echo {}", s)).run().unwrap();
}
```

This function _appears_ to work when `s` is a well-behaved string like
`"foo"` or `"foo bar"`. You might notice something wrong if you try
`"foo   bar"`, because those three spaces will collapse into one in the
output. But the real problem is a string like `"; rm -rf /"`. The resulting
command will print a newline and then try to delete your entire hard drive.
Any function resembling `echo_string`, exposed to any kind of untrusted
input, becomes a serious security issue.

It's possible to work around these issues by escaping special characters,
but escaping is tricky, and it's difficult to test that you've covered
every character. Special characters are also _platform-specific_, making it
even harder to get decent test coverage. The difficulty of doing all this
correctly will generally outweigh any convenience provided by the `duct_sh`
crate itself.

For these reasons, in addition to the portability concerned discussed
above, most programs intended for production should prefer `duct` over
`duct_sh`. Since `duct` avoids invoking the shell at all, it isn't usually
vulnerable to shell injection.
