//! A convenience wrapper around the `duct` crate for building commands out of
//! shell strings. Duct normally executes commands directly, without going
//! through a shell at all. This is preferable where possible, because it avoids
//! tricky whitespace issues and shell injection vulnerabilities. However,
//! sometimes you need access to more esoteric shell features (e.g. shell
//! builtins like `source` and `exec`, or process substitution with `<()`), and
//! other times you're just stuck with a string of shell code that you have to
//! run somehow.
//!
//! In these situations, `duct_sh` is a "cross-platform" way to run shell
//! commands, in combination with all the usual features of Duct.
//! "Cross-platform" is in scare quotes, however, because shell code is
//! necessarily platform-specific. The typical Bourne-like shells on Unix and
//! the cmd.exe shell on Windows systems do have a lot in common, including the
//! `|` and `>` operators, but they diverge very quickly when you start to look
//! at the details. For that reason, seriously cross-platform programs should
//! avoid shell code as much as possible.
//!
//! # Example
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(windows) { return Ok(()); }
//! // Execute a static string of shell code.
//! let output = duct_sh::sh("echo $MSG | sed s/i/a/").env("MSG", "hi").read()?;
//! assert_eq!(output, "ha");
//!
//! // Execute a dynamic string of shell code. Note that this requires the
//! // "sh_dangerous" function. See the Security section below.
//! let arg = "hi";
//! let command = format!("echo {} | sed s/i/a/", arg);
//! let output = duct_sh::sh_dangerous(&command).read()?;
//! assert_eq!(output, "ha");
//! # Ok(()) }
//! ```
//!
//! # Security
//!
//! The `sh` function is restricted to static strings. The `sh_dangerous`
//! function does exactly the same thing, but it accepts dynamic strings. The
//! scary name is because of security issues related to shell injection.
//! Consider this innocent-looking function:
//!
//! ```
//! fn echo_string(s: &str) {
//!     duct_sh::sh_dangerous(format!("echo {}", s)).run().unwrap();
//! }
//! ```
//!
//! This function _appears_ to work when `s` is a well-behaved string like
//! `"foo"` or `"foo bar"`. You might notice something wrong if you try
//! `"foo   bar"`, because those three spaces will collapse into one in the
//! output. But the real problem is a string like `"; rm -rf /"`. The resulting
//! command will print a newline and then try to delete your entire hard drive.
//! Any function resembling `echo_string`, exposed to any kind of untrusted
//! input, becomes a serious security issue.
//!
//! It's possible to work around these issues by escaping special characters,
//! but escaping is tricky, and it's difficult to test that you've covered
//! every character. Special characters are also _platform-specific_, making it
//! even harder to get decent test coverage. The difficulty of doing all this
//! correctly will generally outweigh any convenience provided by the `duct_sh`
//! crate itself.
//!
//! For these reasons, in addition to the portability concerned discussed
//! above, most programs intended for production should prefer `duct` over
//! `duct_sh`. Since `duct` avoids invoking the shell at all, it isn't usually
//! vulnerable to shell injection.

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
    use super::*;

    #[test]
    fn test_sh() {
        let out = sh("echo hi").read().unwrap();
        assert_eq!("hi", out);
    }

    #[test]
    fn test_sh_dangerous() {
        let out = sh_dangerous("echo hi".to_owned()).read().unwrap();
        assert_eq!("hi", out);
    }
}
