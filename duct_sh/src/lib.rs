//! The `sh` function was originally included in the `duct` library itself.
//! Because of safety concerns, we decided to split that function into `sh`
//! (taking only static strings) and `sh_dangerous` (taking any string). That in
//! turn raised a portability problem: duct is a
//! [multi-language](https://github.com/oconnor663/duct.py) library, and most
//! languages can't distinguish string lifetimes the way that Rust can. As an
//! experiment, we're splitting these functions into their own crate, with the
//! intention of keeping them Rust-only.
//!
//! I don't know if we'll keep this arrangement, but here are some other
//! points in favor:
//!
//! - Simple `sh` commands are nice when you first write them, but it feels
//!   annoying to rewrite them as `cmd!` once you need to introduce a variable
//!   somewhere. That annoyance is pressure to do something evil.
//! - Legitimate use cases for `sh_dangerous` in small scripts is rare. The
//!   common use case is something like a build tool, where the user is expected
//!   to run arbitrary shell commands through the tool. Importing an extra crate
//!   (or just copying the whole function) is less of a big deal in the source
//!   code of a build tool than it is in a small script.
//! - Many languages have standard library support for launching shell commands.
//!   Rust doesn't, and so `duct_sh` is more valuable in Rust than it would by
//!   in say Python.

extern crate duct;

use std::ffi::OsString;

/// Create a command from a static string of shell code.
///
/// This invokes the operating system's shell to execute the string: `/bin/sh`
/// on Unix-like systems and `cmd.exe` (or `%COMSPEC%`) on Windows. This can be
/// very convenient sometimes, especially in small scripts and examples. You
/// don't need to quote each argument, and all the operators like `|` and `>`
/// work as usual.
///
/// `sh` avoids security issues by accepting only static strings. If you need to
/// build shell commands at runtime, read the documentation for `sh_dangerous`.
///
/// # Example
///
/// ```
/// use duct_sh::sh;
///
/// let output = sh("echo foo bar baz").read();
///
/// assert_eq!("foo bar baz", output.unwrap());
/// ```
pub fn sh(command: &'static str) -> duct::Expression {
    let argv = shell_command_argv(command.into());
    duct::cmd(&argv[0], &argv[1..])
}

/// Create a command from any string of shell code. This works like `sh`, but
/// it's not limited to static strings.
///
/// # Warning
///
/// Building shell commands out of user input raises serious security problems,
/// in addition to ordinary whitespace and escaping issues, so this function has
/// a scary name. If someone sneaks an argument like `$(evil_command.sh)` into
/// your shell string, you will execute the evil command without meaning to.
/// Shell escaping is tricky and platform-dependent, and using `duct::cmd!` is
/// _much_ safer when it's an option.
///
/// # Example
///
/// ```
/// use duct_sh::sh_dangerous;
///
/// let my_command = "echo".to_string() + " foo bar baz";
/// let output = sh_dangerous(my_command).read();
///
/// assert_eq!("foo bar baz", output.unwrap());
/// ```
pub fn sh_dangerous<T: Into<OsString>>(command: T) -> duct::Expression {
    let argv = shell_command_argv(command.into());
    duct::cmd(&argv[0], &argv[1..])
}

#[cfg(unix)]
fn shell_command_argv(command: OsString) -> Vec<OsString> {
    vec!["/bin/sh".into(), "-c".into(), command]
}

#[cfg(windows)]
fn shell_command_argv(command: OsString) -> Vec<OsString> {
    let comspec = std::env::var_os("COMSPEC").unwrap_or_else(|| "cmd.exe".into());
    vec![comspec, "/C".into(), command]
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sh() {
        let out = ::sh("echo hi").read().unwrap();
        assert_eq!("hi", out);
    }

    #[test]
    fn test_sh_dangerous() {
        let out = ::sh_dangerous("echo hi".to_owned()).read().unwrap();
        assert_eq!("hi", out);
    }
}
