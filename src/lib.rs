//! A cross-platform library for running child processes and building
//! pipelines.
//!
//! `duct` wants to make shelling out in Rust as easy and flexible as it is in
//! Bash. It takes care of [gotchas and
//! inconsistencies](https://github.com/oconnor663/duct.py/blob/master/spec.md)
//! in the way different platforms shell out. And it's a cross-language library;
//! the [original implementation](https://github.com/oconnor663/duct.py) is in
//! Python, with an identical API.
//!
//! - [Docs](https://docs.rs/duct)
//! - [Crate](https://crates.io/crates/duct)
//! - [Repo](https://github.com/oconnor663/duct.rs)
//!
//! # Changelog
//!
//! - Version 0.11 introduced the `before_spawn` method.
//! - Version 0.10 changed how environment variable casing is handled on Windows.
//!   See the docs for `env_remove`.
//! - Version 0.9 removed the `sh` function. It now lives in its own crate, `duct_sh`.
//!
//! # Example
//!
//! `duct` tries to be as concise as possible, so that you don't wish you were
//! back writing shell scripts. At the same time, it's explicit about what
//! happens to output, and strict about error codes in child processes.
//!
//! ```no_run
//! # #[macro_use]
//! # use duct::cmd;
//! # use std::io::BufReader;
//! # use std::io::prelude::*;
//! # use std::error::Error;
//! # fn main() -> Result<(), Box<dyn Error>> {
//! // Read the name of the current git branch. If git exits with an error
//! // code here (because we're not in a git repo, for example), `read` will
//! // return an error too.
//! let current_branch = cmd!("git", "symbolic-ref", "--short", "HEAD").read()?;
//!
//! // Log the current branch, with git taking over the terminal as usual.
//! // The `cmd` function works just like the `cmd!` macro, but it takes a
//! // collection instead of a variable list of arguments.
//! let args = &["log", &current_branch];
//! cmd("git", args).run()?;
//!
//! // Log again, but this time read the output from a pipe of our own. We
//! // use the os_pipe crate to create the pipe, but any type implementing
//! // IntoRawFd works here, including File.
//! let (pipe_reader, pipe_writer) = os_pipe::pipe()?;
//! let child = cmd!("git", "log", "--oneline").stdout_file(pipe_writer).start()?;
//! for line in BufReader::new(pipe_reader).lines() {
//!     assert!(!line?.contains("heck"), "profanity filter triggered");
//! }
//! #     Ok(())
//! # }
//! ```
//!
//! `duct` uses [`os_pipe`](https://github.com/oconnor663/os_pipe.rs)
//! internally, and the docs for that one include a [big
//! example](https://docs.rs/os_pipe#example) that takes a dozen lines of code
//! to read both stdout and stderr from a child process. `duct` can do that in
//! one (moderately long) line:
//!
//! ```
//! # use duct::cmd;
//! # fn main() {
//! # if cfg!(not(windows)) {
//! let output = cmd!("sh", "-c", "echo foo && echo bar 2>&1").stderr_to_stdout().read().unwrap();
//!
//! assert!(output.split_whitespace().eq(vec!["foo", "bar"]));
//! # }
//! # }
//! ```

use once_cell::sync::OnceCell;
use shared_child::SharedChild;
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::mem;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;

#[cfg(not(windows))]
use std::os::unix::prelude::*;
#[cfg(windows)]
use std::os::windows::prelude::*;

/// Unix-specific extensions to duct, for sending signals.
#[cfg(unix)]
pub mod unix;

// enums defined below
use ExpressionInner::*;
use IoExpressionInner::*;

/// Create a command given a program name and a collection of arguments. See
/// also the [`cmd!`](macro.cmd.html) macro, which doesn't require a collection.
///
/// # Example
///
/// ```
/// use duct::cmd;
///
/// let args = vec!["foo", "bar", "baz"];
///
/// # // NOTE: Normally this wouldn't work on Windows, but we have an "echo"
/// # // binary that gets built for our main tests, and it's sitting around by
/// # // the time we get here. If this ever stops working, then we can disable
/// # // the tests that depend on it.
/// let output = cmd("echo", &args).read();
///
/// assert_eq!("foo bar baz", output.unwrap());
/// ```
pub fn cmd<T, U, V>(program: T, args: U) -> Expression
where
    T: ToExecutable,
    U: IntoIterator<Item = V>,
    V: Into<OsString>,
{
    let mut argv_vec = Vec::new();
    argv_vec.push(program.to_executable());
    argv_vec.extend(args.into_iter().map(Into::<OsString>::into));
    Expression::new(Cmd(argv_vec))
}

/// Create a command with any number of of positional arguments, which may be
/// different types (anything that implements
/// [`Into<OsString>`](https://doc.rust-lang.org/std/convert/trait.From.html)).
/// See also the [`cmd`](fn.cmd.html) function, which takes a collection of
/// arguments.
///
/// # Example
///
/// ```
///
/// use duct::cmd;
/// use std::path::Path;
///
/// fn main() {
///     let arg1 = "foo";
///     let arg2 = "bar".to_owned();
///     let arg3 = Path::new("baz");
///
///     let output = cmd!("echo", arg1, arg2, arg3).read();
///
///     assert_eq!("foo bar baz", output.unwrap());
/// }
/// ```
#[macro_export]
macro_rules! cmd {
    ( $program:expr $(, $arg:expr )* $(,)? ) => {
        {
            use std::ffi::OsString;
            let args: &[OsString] = &[$( Into::<OsString>::into($arg) ),*];
            $crate::cmd($program, args)
        }
    };
}

/// The central objects in `duct`, Expressions are created with
/// [`cmd`](fn.cmd.html) or [`cmd!`](macro.cmd.html), combined with
/// [`pipe`](struct.Expression.html#method.pipe), and finally executed with
/// [`start`](struct.Expression.html#method.start),
/// [`run`](struct.Expression.html#method.run), or
/// [`read`](struct.Expression.html#method.read). They also support several
/// methods to control their execution, like
/// [`input`](struct.Expression.html#method.input),
/// [`env`](struct.Expression.html#method.env), and
/// [`unchecked`](struct.Expression.html#method.unchecked).
///
/// Expressions are immutable, and they do a lot of
/// [`Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html) sharing
/// internally, so all of the methods below take `&self` and return a new
/// `Expression` cheaply.
///
/// Expressions using `pipe` form trees, and the order in which you call
/// different methods can matter, just like it matters where you put
/// redirections in Bash. For example, each of these expressions suppresses
/// output differently:
///
/// ```no_run
/// # use duct::cmd;
/// # fn main() -> std::io::Result<()> {
/// // Only suppress stderr on the left side.
/// cmd!("foo").stderr_null().pipe(cmd!("bar")).run()?;
///
/// // Only suppress stderr on the right side.
/// cmd!("foo").pipe(cmd!("bar").stderr_null()).run()?;
///
/// // Suppress stderr on both sides.
/// cmd!("foo").pipe(cmd!("bar")).stderr_null().run()?;
/// # Ok(())
/// # }
/// ```
#[derive(Clone, Debug)]
#[must_use]
pub struct Expression(Arc<ExpressionInner>);

impl Expression {
    /// Execute an expression, wait for it to complete, and return a
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// object containing the results. Nothing is captured by default, but if
    /// you build the expression with
    /// [`stdout_capture`](struct.Expression.html#method.stdout_capture) or
    /// [`stderr_capture`](struct.Expression.html#method.stderr_capture) then
    /// the `Output` will hold those captured bytes.
    ///
    /// # Errors
    ///
    /// In addition to all the IO errors possible with
    /// [`std::process::Command`](https://doc.rust-lang.org/std/process/struct.Command.html),
    /// `run` will return an
    /// [`ErrorKind::Other`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html)
    /// IO error if child returns a non-zero exit status. To suppress this error
    /// and return an `Output` even when the exit status is non-zero, use the
    /// [`unchecked`](struct.Expression.html#method.unchecked) method.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "hi").stdout_capture().run().unwrap();
    /// assert_eq!(b"hi\n".to_vec(), output.stdout);
    /// # }
    /// # }
    /// ```
    pub fn run(&self) -> io::Result<Output> {
        self.start()?.into_output()
    }

    /// Execute an expression, capture its standard output, and return the
    /// captured output as a `String`. This is a convenience wrapper around
    /// [`run`](struct.Expression.html#method.run). Like backticks and `$()` in
    /// the shell, `read` trims trailing newlines.
    ///
    /// # Errors
    ///
    /// In addition to all the errors possible with
    /// [`run`](struct.Expression.html#method.run), `read` will return an
    /// [`ErrorKind::InvalidData`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html)
    /// IO error if the captured bytes aren't valid UTF-8.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "hi").stdout_capture().read().unwrap();
    /// assert_eq!("hi", output);
    /// # }
    /// # }
    /// ```
    pub fn read(&self) -> io::Result<String> {
        let output = self.stdout_capture().run()?;
        if let Ok(output_str) = std::str::from_utf8(&output.stdout) {
            Ok(trim_end_newlines(output_str).to_owned())
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "stdout is not valid UTF-8",
            ))
        }
    }

    /// Start running an expression, and immediately return a
    /// [`Handle`](struct.Handle.html) that represents all the child processes.
    /// This is analogous to the
    /// [`spawn`](https://doc.rust-lang.org/std/process/struct.Command.html#method.spawn)
    /// method in the standard library. The `Handle` may be shared between
    /// multiple threads.
    ///
    /// # Errors
    ///
    /// In addition to all the errors possible with
    /// [`std::process::Command::spawn`](https://doc.rust-lang.org/std/process/struct.Command.html#method.spawn),
    /// `start` can return errors from opening pipes and files. However, `start`
    /// will never return an error if a child process has already started. In
    /// particular, if the left side of a pipe expression starts successfully,
    /// `start` will always return `Ok`. Any errors that happen on the right
    /// side will be saved and returned later by the wait methods. That makes it
    /// safe for callers to short circuit on `start` errors without the risk of
    /// leaking processes.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let handle = cmd!("echo", "hi").stdout_capture().start().unwrap();
    /// let output = handle.wait().unwrap();
    /// assert_eq!(b"hi\n".to_vec(), output.stdout);
    /// # }
    /// # }
    /// ```
    pub fn start(&self) -> io::Result<Handle> {
        let (context, stdout_reader, stderr_reader) = IoContext::new()?;
        Ok(Handle {
            inner: self.0.start(context)?,
            result: OnceCell::new(),
            readers: Mutex::new(Some((stdout_reader, stderr_reader))),
        })
    }

    /// Join two expressions into a pipe expression, where the standard output
    /// of the left will be hooked up to the standard input of the right, like
    /// `|` in the shell.
    ///
    /// # Errors
    ///
    /// During execution, if one side of the pipe returns a non-zero exit
    /// status, that becomes the status of the whole pipe, similar to Bash's
    /// `pipefail` option. If both sides return non-zero, and one of them is
    /// [`unchecked`](struct.Expression.html#method.unchecked), then the checked
    /// side wins. Otherwise the right side wins.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "hi").pipe(cmd!("sed", "s/h/p/")).read();
    /// assert_eq!("pi", output.unwrap());
    /// # }
    /// # }
    /// ```
    pub fn pipe<T: Into<Expression>>(&self, right: T) -> Expression {
        Self::new(Pipe(self.clone(), right.into()))
    }

    /// Use bytes or a string as input for an expression, like `<<<` in the
    /// shell. A worker thread will write the input at runtime.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<Vec<u8>>. Here's a string.
    /// let output = cmd!("cat").stdin_bytes("foo").read().unwrap();
    /// assert_eq!("foo", output);
    ///
    /// // And here's a byte slice.
    /// let output = cmd!("cat").stdin_bytes(&b"foo"[..]).read().unwrap();
    /// assert_eq!("foo", output);
    /// # }
    /// # }
    /// ```
    pub fn stdin_bytes<T: Into<Vec<u8>>>(&self, bytes: T) -> Expression {
        Self::new(Io(StdinBytes(Arc::new(bytes.into())), self.clone()))
    }

    /// Open a file at the given path and use it as input for an expression,
    /// like `<` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let output = cmd!("head", "-c", "3").stdin_path("/dev/zero").read().unwrap();
    /// assert_eq!("\0\0\0", output);
    /// # }
    /// # }
    /// ```
    pub fn stdin_path<T: Into<PathBuf>>(&self, path: T) -> Expression {
        Self::new(Io(StdinPath(path.into()), self.clone()))
    }

    /// Use an already opened file or pipe as input for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let input_file = std::fs::File::open("/dev/zero").unwrap();
    /// let output = cmd!("head", "-c", "3").stdin_file(input_file).read().unwrap();
    /// assert_eq!("\0\0\0", output);
    /// # }
    /// # }
    /// ```
    #[cfg(not(windows))]
    pub fn stdin_file<T: IntoRawFd>(&self, file: T) -> Expression {
        Self::new(Io(StdinFile(into_file(file)), self.clone()))
    }
    #[cfg(windows)]
    pub fn stdin_file<T: IntoRawHandle>(&self, file: T) -> Expression {
        Self::new(Io(StdinFile(into_file(file)), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as input for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("cat").stdin_null().read().unwrap();
    /// assert_eq!("", output);
    /// # }
    /// # }
    /// ```
    pub fn stdin_null(&self) -> Expression {
        Self::new(Io(StdinNull, self.clone()))
    }

    /// Open a file at the given path and use it as output for an expression,
    /// like `>` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let path = cmd!("mktemp").read().unwrap();
    /// cmd!("echo", "wee").stdout_path(&path).run().unwrap();
    /// let mut output = String::new();
    /// std::fs::File::open(&path).unwrap().read_to_string(&mut output).unwrap();
    /// assert_eq!("wee\n", output);
    /// # }
    /// # }
    /// ```
    pub fn stdout_path<T: Into<PathBuf>>(&self, path: T) -> Expression {
        Self::new(Io(StdoutPath(path.into()), self.clone()))
    }

    /// Use an already opened file or pipe as output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// let path = cmd!("mktemp").read().unwrap();
    /// let file = std::fs::File::create(&path).unwrap();
    /// cmd!("echo", "wee").stdout_file(file).run().unwrap();
    /// let mut output = String::new();
    /// std::fs::File::open(&path).unwrap().read_to_string(&mut output).unwrap();
    /// assert_eq!("wee\n", output);
    /// # }
    /// # }
    /// ```
    #[cfg(not(windows))]
    pub fn stdout_file<T: IntoRawFd>(&self, file: T) -> Expression {
        Self::new(Io(StdoutFile(into_file(file)), self.clone()))
    }
    #[cfg(windows)]
    pub fn stdout_file<T: IntoRawHandle>(&self, file: T) -> Expression {
        Self::new(Io(StdoutFile(into_file(file)), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// // This echo command won't print anything.
    /// cmd!("echo", "foo", "bar", "baz").stdout_null().run().unwrap();
    ///
    /// // And you won't get anything even if you try to read its output! The
    /// // null redirect happens farther down in the expression tree than the
    /// // implicit `stdout_capture`, and so it takes precedence.
    /// let output = cmd!("echo", "foo", "bar", "baz").stdout_null().read().unwrap();
    /// assert_eq!("", output);
    /// # }
    /// ```
    pub fn stdout_null(&self) -> Expression {
        Self::new(Io(StdoutNull, self.clone()))
    }

    /// Capture the standard output of an expression. The captured bytes will be
    /// available on the `stdout` field of the
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// object returned by [`run`](struct.Expression.html#method.run) or
    /// [`wait`](struct.Handle.html#method.wait). In the simplest cases,
    /// [`read`](struct.Expression.html#method.read) can be more convenient.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // The most direct way to read stdout bytes is `stdout_capture`.
    /// let output1 = cmd!("echo", "foo").stdout_capture().run().unwrap().stdout;
    /// assert_eq!(&b"foo\n"[..], &output1[..]);
    ///
    /// // The `read` method is a shorthand for `stdout_capture`, and it also
    /// // does string parsing and newline trimming.
    /// let output2 = cmd!("echo", "foo").read().unwrap();
    /// assert_eq!("foo", output2)
    /// # }
    /// # }
    /// ```
    pub fn stdout_capture(&self) -> Expression {
        Self::new(Io(StdoutCapture, self.clone()))
    }

    /// Join the standard output of an expression to its standard error pipe,
    /// similar to `1>&2` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "foo").stdout_to_stderr().stderr_capture().run().unwrap();
    /// assert_eq!(&b"foo\n"[..], &output.stderr[..]);
    /// # }
    /// # }
    /// ```
    pub fn stdout_to_stderr(&self) -> Expression {
        Self::new(Io(StdoutToStderr, self.clone()))
    }

    /// Open a file at the given path and use it as error output for an
    /// expression, like `2>` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let path = cmd!("mktemp").read().unwrap();
    /// cmd!("sh", "-c", "echo wee >&2").stderr_path(&path).run().unwrap();
    /// let mut error_output = String::new();
    /// std::fs::File::open(&path).unwrap().read_to_string(&mut error_output).unwrap();
    /// assert_eq!("wee\n", error_output);
    /// # }
    /// # }
    /// ```
    pub fn stderr_path<T: Into<PathBuf>>(&self, path: T) -> Expression {
        Self::new(Io(StderrPath(path.into()), self.clone()))
    }

    /// Use an already opened file or pipe as error output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// let path = cmd!("mktemp").read().unwrap();
    /// let file = std::fs::File::create(&path).unwrap();
    /// cmd!("sh", "-c", "echo wee >&2").stderr_file(file).run().unwrap();
    /// let mut error_output = String::new();
    /// std::fs::File::open(&path).unwrap().read_to_string(&mut error_output).unwrap();
    /// assert_eq!("wee\n", error_output);
    /// # }
    /// # }
    /// ```
    #[cfg(not(windows))]
    pub fn stderr_file<T: IntoRawFd>(&self, file: T) -> Expression {
        Self::new(Io(StderrFile(into_file(file)), self.clone()))
    }
    #[cfg(windows)]
    pub fn stderr_file<T: IntoRawHandle>(&self, file: T) -> Expression {
        Self::new(Io(StderrFile(into_file(file)), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as error output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // This echo-to-stderr command won't print anything.
    /// cmd!("sh", "-c", "echo foo bar baz >&2").stderr_null().run().unwrap();
    /// # }
    /// # }
    /// ```
    pub fn stderr_null(&self) -> Expression {
        Self::new(Io(StderrNull, self.clone()))
    }

    /// Capture the error output of an expression. The captured bytes will be
    /// available on the `stderr` field of the `Output` object returned by
    /// [`run`](struct.Expression.html#method.run) or
    /// [`wait`](struct.Handle.html#method.wait).
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output_obj = cmd!("sh", "-c", "echo foo >&2").stderr_capture().run().unwrap();
    /// assert_eq!(&b"foo\n"[..], &output_obj.stderr[..]);
    /// # }
    /// # }
    /// ```
    pub fn stderr_capture(&self) -> Expression {
        Self::new(Io(StderrCapture, self.clone()))
    }

    /// Join the standard error of an expression to its standard output pipe,
    /// similar to `2>&1` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let error_output = cmd!("sh", "-c", "echo foo >&2").stderr_to_stdout().read().unwrap();
    /// assert_eq!("foo", error_output);
    /// # }
    /// # }
    /// ```
    pub fn stderr_to_stdout(&self) -> Expression {
        Self::new(Io(StderrToStdout, self.clone()))
    }

    /// Swap the stdout and stderr of an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("sh", "-c", "echo foo && echo bar >&2")
    ///     .stdout_stderr_swap()
    ///     .stdout_capture()
    ///     .stderr_capture()
    ///     .run()
    ///     .unwrap();
    /// assert_eq!(b"bar\n", &*output.stdout);
    /// assert_eq!(b"foo\n", &*output.stderr);
    /// # }
    /// # }
    /// ```
    pub fn stdout_stderr_swap(&self) -> Expression {
        Self::new(Io(StdoutStderrSwap, self.clone()))
    }

    /// Set the working directory where the expression will execute.
    ///
    /// Note that in some languages (Rust and Python at least), there are tricky
    /// platform differences in the way relative exe paths interact with child
    /// working directories. In particular, the exe path will be interpreted
    /// relative to the child dir on Unix, but relative to the parent dir on
    /// Windows. `duct` considers the Windows behavior correct, so in order to
    /// get that behavior consistently it calls
    /// [`std::fs::canonicalize`](https://doc.rust-lang.org/std/fs/fn.canonicalize.html)
    /// on relative exe paths when `dir` is in use. Paths in this sense are any
    /// program name containing a path separator, regardless of the type. (Note
    /// also that `Path` and `PathBuf` program names get a `./` prepended to
    /// them automatically by the [`ToExecutable`](trait.ToExecutable.html)
    /// trait, and so will always contain a separator.)
    ///
    /// # Errors
    ///
    /// Canonicalization can fail on some filesystems, or if the current
    /// directory has been removed, and
    /// [`run`](struct.Expression.html#method.run) will return those errors
    /// rather than trying any sneaky workarounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("pwd").dir("/").read().unwrap();
    /// assert_eq!("/", output);
    /// # }
    /// # }
    /// ```
    pub fn dir<T: Into<PathBuf>>(&self, path: T) -> Expression {
        Self::new(Io(Dir(path.into()), self.clone()))
    }

    /// Set a variable in the expression's environment.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("sh", "-c", "echo $FOO").env("FOO", "bar").read().unwrap();
    /// assert_eq!("bar", output);
    /// # }
    /// # }
    /// ```
    pub fn env<T, U>(&self, name: T, val: U) -> Expression
    where
        T: Into<OsString>,
        U: Into<OsString>,
    {
        Self::new(Io(
            Env(canonicalize_env_var_name(name.into()), val.into()),
            self.clone(),
        ))
    }

    /// Remove a variable from the expression's environment.
    ///
    /// Note that all the environment functions try to do whatever the platform
    /// does with respect to case sensitivity. That means that
    /// `env_remove("foo")` will unset the uppercase variable `FOO` on Windows,
    /// but not on Unix.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// std::env::set_var("TESTING", "true");
    /// let output = cmd!("sh", "-c", "echo a${TESTING}b")
    ///     .env_remove("TESTING")
    ///     .read()
    ///     .unwrap();
    /// assert_eq!("ab", output);
    /// # }
    /// # }
    /// ```
    pub fn env_remove<T>(&self, name: T) -> Expression
    where
        T: Into<OsString>,
    {
        Self::new(Io(
            EnvRemove(canonicalize_env_var_name(name.into())),
            self.clone(),
        ))
    }

    /// Set the expression's entire environment, from a collection of name-value
    /// pairs (like a `HashMap`). You can use this method to clear specific
    /// variables for example, by collecting the parent's environment, removing
    /// some names from the collection, and passing the result to `full_env`.
    /// Note that some environment variables are required for normal program
    /// execution (like `SystemRoot` on Windows), so copying the parent's
    /// environment is usually preferable to starting with an empty one.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// # use std::collections::HashMap;
    /// # if cfg!(not(windows)) {
    /// let mut env_map: HashMap<_, _> = std::env::vars().collect();
    /// env_map.insert("FOO".into(), "bar".into());
    /// let output = cmd!("sh", "-c", "echo $FOO").full_env(&env_map).read().unwrap();
    /// assert_eq!("bar", output);
    /// // The IntoIterator/Into<OsString> bounds are pretty flexible. Passing
    /// // by value works here too.
    /// let output = cmd!("sh", "-c", "echo $FOO").full_env(env_map).read().unwrap();
    /// assert_eq!("bar", output);
    /// # }
    /// # }
    /// ```
    pub fn full_env<T, U, V>(&self, name_vals: T) -> Expression
    where
        T: IntoIterator<Item = (U, V)>,
        U: Into<OsString>,
        V: Into<OsString>,
    {
        let env_map = name_vals
            .into_iter()
            .map(|(k, v)| (canonicalize_env_var_name(k.into()), v.into()))
            .collect();
        Self::new(Io(FullEnv(env_map), self.clone()))
    }

    /// Prevent a non-zero exit status from causing
    /// [`run`](struct.Expression.html#method.run) or
    /// [`read`](struct.Expression.html#method.read) to return an error. The
    /// unchecked exit code will still be there on the `Output` returned by
    /// `run`; its value doesn't change.
    ///
    /// "Uncheckedness" sticks to an exit code as it bubbles up through
    /// complicated pipelines, but it doesn't "infect" other exit codes. So for
    /// example, if only one sub-expression in a pipe has `unchecked`, then
    /// errors returned by the other side will still be checked. That said,
    /// most commonly you'll just call `unchecked` right before `run`, and
    /// it'll apply to an entire expression.
    ///
    /// # Example
    ///
    /// Note the differences among these three cases:
    ///
    /// ```no_run
    /// # use duct::cmd;
    /// # fn main() -> std::io::Result<()> {
    /// // Don't check errors on the left side.
    /// cmd!("foo").unchecked().pipe(cmd!("bar")).run()?;
    ///
    /// // Don't check errors on the right side.
    /// cmd!("foo").pipe(cmd!("bar").unchecked()).run()?;
    ///
    /// // Don't check errors on either side.
    /// cmd!("foo").pipe(cmd!("bar")).unchecked().run()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn unchecked(&self) -> Expression {
        Self::new(Io(Unchecked, self.clone()))
    }

    /// Add a hook for modifying
    /// [`std::process::Command`](https://doc.rust-lang.org/std/process/struct.Command.html)
    /// objects immediately before they're executed.
    ///
    /// The hook is called for each command in its sub-expression, and each time the expression is
    /// executed. The call happens after other features like `stdout` and `env` have been applied,
    /// so any changes made by the hook take priority. More than one hook can be added, in which
    /// case the innermost is executed last. For example, if one call to `before_spawn` is applied
    /// to an entire pipe expression, and another call is applied to just one command within the
    /// pipe, the hook for the entire pipeline will be called first over the command where both
    /// hooks apply.
    ///
    /// This is intended for rare and tricky cases, like callers who want to change the group ID of
    /// their child processes, or who want to run code in `before_exec`. Most callers shouldn't
    /// need to use it.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # fn main() {
    /// let output = cmd!("echo", "foo")
    ///     .before_spawn(|cmd| {
    ///         // Sneakily add an extra argument.
    ///         cmd.arg("bar");
    ///         Ok(())
    ///     })
    ///     .read()
    ///     .unwrap();
    /// assert_eq!("foo bar", output);
    /// # }
    /// ```
    pub fn before_spawn<F>(&self, hook: F) -> Expression
    where
        F: Fn(&mut Command) -> io::Result<()> + Send + Sync + 'static,
    {
        Self::new(Io(BeforeSpawn(BeforeSpawnHook::new(hook)), self.clone()))
    }

    fn new(inner: ExpressionInner) -> Expression {
        Expression(Arc::new(inner))
    }
}

// Implemening Into<Expression> for references lets us accept both references
// and values in `pipe`.
impl<'a> From<&'a Expression> for Expression {
    fn from(expr: &Expression) -> Expression {
        expr.clone()
    }
}

/// A handle to a running expression, returned by the
/// [`start`](struct.Expression.html#method.start) method. Calling `start`
/// followed by [`output`](struct.Handle.html#method.output) on the handle is
/// equivalent to [`run`](struct.Expression.html#method.run). Note that unlike
/// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html),
/// most of the methods on `Handle` take `&self` rather than `&mut self`, and a
/// `Handle` may be shared between multiple threads.
///
/// Like `std::process::Child`, `Handle` doesn't do anything special in its
/// destructor. If a `Handle` goes out of scope without calling
/// [`wait`](struct.Handle.html#method.wait) or similar, child processes and
/// background threads will keep running, and they'll [leave
/// zombies](https://en.wikipedia.org/wiki/Resource_leak#Causes) when they
/// exit.
///
/// See the [`shared_child`](https://github.com/oconnor663/shared_child.rs)
/// crate for implementation details behind making handles thread safe.
#[derive(Debug)]
pub struct Handle {
    inner: HandleInner,
    result: OnceCell<io::Result<Output>>,
    readers: Mutex<Option<(ReaderThread, ReaderThread)>>,
}

impl Handle {
    /// Wait for the running expression to finish, and return a reference to its
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html).
    /// Multiple threads may wait at the same time.
    pub fn wait(&self) -> io::Result<&Output> {
        let status = self
            .inner
            .wait(WaitMode::Blocking)?
            .expect("blocking wait can't return None");
        // The expression has exited. See if we need to collect its output
        // result, or if another caller has already done it. Do this inside the
        // readers lock, to avoid racing to fill the result.
        let mut readers_lock = self.readers.lock().expect("readers lock poisoned");
        if self.result.get().is_none() {
            // We're holding the readers lock, and we're the thread that needs
            // to collect the output. Take the reader threads and join them.
            let (stdout_reader, stderr_reader) = readers_lock
                .take()
                .expect("readers taken without filling result");
            let stdout_result = stdout_reader.join().expect("stdout reader panic");
            let stderr_result = stderr_reader.join().expect("stderr reader panic");
            let final_result = match (stdout_result, stderr_result) {
                // The highest priority result is IO errors in the reader
                // threads.
                (Err(err), _) | (_, Err(err)) => Err(err),

                // Then checked status errors.
                _ if status.is_checked_error() => {
                    Err(io::Error::new(io::ErrorKind::Other, status.message()))
                }

                // And finally the successful output.
                (Ok(stdout), Ok(stderr)) => Ok(Output {
                    status: status.status,
                    stdout: stdout,
                    stderr: stderr,
                }),
            };
            self.result
                .set(final_result)
                .expect("result already filled outside the readers lock");
        }
        // The result has been collected, whether or not we were the caller that
        // collected it. Return a reference.
        match self.result.get().expect("result not filled") {
            Ok(output) => Ok(output),
            Err(err) => Err(clone_io_error(err)),
        }
    }

    /// Check whether the running expression is finished. If it is, return a
    /// reference to its
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html).
    /// If it's still running, return `Ok(None)`.
    pub fn try_wait(&self) -> io::Result<Option<&Output>> {
        if self.inner.wait(WaitMode::Nonblocking)?.is_none() {
            Ok(None)
        } else {
            self.wait().map(Some)
        }
    }

    /// Wait for the running expression to finish, and then return a
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// object containing the results, including any captured output. This
    /// consumes the `Handle`. Calling
    /// [`start`](struct.Expression.html#method.start) followed by
    /// `into_output` is equivalent to
    /// [`run`](struct.Expression.html#method.run).
    pub fn into_output(self) -> io::Result<Output> {
        self.wait()?;
        self.result
            .into_inner()
            .expect("wait didn't set the result")
    }

    /// Kill the running expression.
    pub fn kill(&self) -> io::Result<()> {
        self.inner.kill()
    }
}

#[derive(Debug)]
enum ExpressionInner {
    Cmd(Vec<OsString>),
    Pipe(Expression, Expression),
    Io(IoExpressionInner, Expression),
}

impl ExpressionInner {
    fn start(&self, context: IoContext) -> io::Result<HandleInner> {
        Ok(match self {
            Cmd(argv) => HandleInner::Child(start_argv(argv, context)?),
            Pipe(left, right) => {
                HandleInner::Pipe(Box::new(PipeHandle::start(left, right, context)?))
            }
            Io(io_inner, expr) => start_io(io_inner, expr, context)?,
        })
    }
}

#[derive(Debug)]
enum HandleInner {
    Child(ChildHandle),
    // If the left side of a pipe fails to start, there's nothing to wait for,
    // and we return an error immediately. But if the right side fails to start,
    // the caller still needs to wait on the left, and we must return a handle.
    // Thus the handle preserves the right side's errors here.
    Pipe(Box<PipeHandle>),
    StdinBytes(Box<StdinBytesHandle>),
    Unchecked(Box<HandleInner>),
}

impl HandleInner {
    fn wait(&self, mode: WaitMode) -> io::Result<Option<ExpressionStatus>> {
        match self {
            HandleInner::Child(child_handle) => child_handle.wait(mode),
            HandleInner::Pipe(pipe_handle) => pipe_handle.wait(mode),
            HandleInner::StdinBytes(stdin_bytes_handle) => stdin_bytes_handle.wait(mode),
            HandleInner::Unchecked(inner_handle) => {
                Ok(inner_handle.wait(mode)?.map(|mut status| {
                    status.checked = false;
                    status
                }))
            }
        }
    }

    fn kill(&self) -> io::Result<()> {
        match self {
            HandleInner::Child(child_handle) => child_handle.kill(),
            HandleInner::Pipe(pipe_handle) => pipe_handle.kill(),
            HandleInner::StdinBytes(stdin_bytes_handle) => stdin_bytes_handle.kill(),
            HandleInner::Unchecked(inner_handle) => inner_handle.kill(),
        }
    }
}

fn start_argv(argv: &[OsString], context: IoContext) -> io::Result<ChildHandle> {
    let exe = canonicalize_exe_path_for_dir(&argv[0], &context)?;
    let mut command = Command::new(exe);
    command.args(&argv[1..]);
    // TODO: Avoid unnecessary dup'ing here.
    command.stdin(context.stdin.into_stdio()?);
    command.stdout(context.stdout.into_stdio()?);
    command.stderr(context.stderr.into_stdio()?);
    if let Some(dir) = context.dir {
        command.current_dir(dir);
    }
    command.env_clear();
    for (name, val) in context.env {
        command.env(name, val);
    }
    // The innermost hooks are pushed last, and we execute them last.
    for hook in context.before_spawn_hooks.iter() {
        hook.call(&mut command)?;
    }
    let shared_child = SharedChild::spawn(&mut command)?;
    let command_string = format!("{:?}", argv);
    Ok(ChildHandle {
        child: shared_child,
        command_string: command_string,
    })
}

#[derive(Debug)]
struct ChildHandle {
    child: shared_child::SharedChild,
    command_string: String,
}

impl ChildHandle {
    fn wait(&self, mode: WaitMode) -> io::Result<Option<ExpressionStatus>> {
        let maybe_status = match mode {
            WaitMode::Blocking => Some(self.child.wait()?),
            WaitMode::Nonblocking => self.child.try_wait()?,
        };
        if let Some(status) = maybe_status {
            Ok(Some(ExpressionStatus {
                status: status,
                checked: true,
                command: self.command_string.clone(),
            }))
        } else {
            Ok(None)
        }
    }

    fn kill(&self) -> io::Result<()> {
        self.child.kill()
    }
}

#[derive(Debug)]
struct PipeHandle {
    left_handle: HandleInner,
    right_handle: HandleInner,
}

impl PipeHandle {
    fn start(left: &Expression, right: &Expression, context: IoContext) -> io::Result<PipeHandle> {
        let (reader, writer) = os_pipe::pipe()?;
        // dup'ing stdin/stdout isn't strictly necessary, but no big deal
        let mut left_context = context.try_clone()?;
        left_context.stdout = IoValue::Handle(into_file(writer));
        let mut right_context = context;
        right_context.stdin = IoValue::Handle(into_file(reader));

        // Errors starting the left side just short-circuit us.
        let left_handle = left.0.start(left_context)?;

        // Now the left side is started. If the right side fails to start, we
        // can't let the left side turn into a zombie. We have to await it, and
        // that means we have to kill it first.
        let right_result = right.0.start(right_context);
        match right_result {
            Ok(right_handle) => Ok(PipeHandle {
                left_handle: left_handle,
                right_handle: right_handle,
            }),
            Err(e) => {
                // Realistically, kill should never return an error. If it
                // does, it's probably due to some bug in this library or one
                // of its dependencies. If that happens just propagate the
                // error and accept that we're probably leaking something.
                left_handle.kill()?;
                // Similarly, this private API wait should never return an
                // error. It might return a non-zero status, but here that's
                // still an Ok result.
                left_handle.wait(WaitMode::Blocking)?;
                Err(e)
            }
        }
    }

    fn wait(&self, mode: WaitMode) -> io::Result<Option<ExpressionStatus>> {
        // Wait on both sides first, without propagating any errors.
        let left_wait_result = self.left_handle.wait(mode);
        let right_wait_result = self.right_handle.wait(mode);

        // Now we deal with errors from either of those waits. The left wait
        // happened first, so that one takes precedence. Note that this is the
        // reverse order of exit status precedence.
        let left_status = left_wait_result?;
        let right_status = right_wait_result?;

        // If both waits succeeded, return one of the two statuses.
        Ok(pipe_status_precedence(left_status, right_status))
    }

    // As with wait, we need to call kill on both sides even if the left side
    // returns an error.
    fn kill(&self) -> io::Result<()> {
        let left_kill_result = self.left_handle.kill();
        let right_kill_result = self.right_handle.kill();
        // As with wait, the left side happened first, so its errors take
        // precedence.
        left_kill_result.and(right_kill_result)
    }
}

// The rules of precedence are:
// 1) If either side unfinished, the result is unfinished.
// 2) Checked errors trump unchecked errors.
// 3) Any errors trump success.
// 4) All else equal, the right side wins.
fn pipe_status_precedence(
    left_maybe_status: Option<ExpressionStatus>,
    right_maybe_status: Option<ExpressionStatus>,
) -> Option<ExpressionStatus> {
    let (left_status, right_status) = match (left_maybe_status, right_maybe_status) {
        (Some(left), Some(right)) => (left, right),
        _ => return None,
    };
    Some(if right_status.is_checked_error() {
        right_status
    } else if left_status.is_checked_error() {
        left_status
    } else if !right_status.status.success() {
        right_status
    } else {
        left_status
    })
}

fn start_io(
    io_inner: &IoExpressionInner,
    expr_inner: &Expression,
    mut context: IoContext,
) -> io::Result<HandleInner> {
    match io_inner {
        StdinBytes(v) => {
            return Ok(HandleInner::StdinBytes(Box::new(StdinBytesHandle::start(
                expr_inner,
                context,
                Arc::clone(v),
            )?)));
        }
        StdinPath(p) => {
            context.stdin = IoValue::Handle(File::open(p)?);
        }
        StdinFile(f) => {
            context.stdin = IoValue::Handle(f.try_clone()?);
        }
        StdinNull => {
            context.stdin = IoValue::Null;
        }
        StdoutPath(p) => {
            context.stdout = IoValue::Handle(File::create(p)?);
        }
        StdoutFile(f) => {
            context.stdout = IoValue::Handle(f.try_clone()?);
        }
        StdoutNull => {
            context.stdout = IoValue::Null;
        }
        StdoutCapture => {
            context.stdout = IoValue::Handle(into_file(context.stdout_capture_pipe.try_clone()?));
        }
        StdoutToStderr => {
            context.stdout = context.stderr.try_clone()?;
        }
        StderrPath(p) => {
            context.stderr = IoValue::Handle(File::create(p)?);
        }
        StderrFile(f) => {
            context.stderr = IoValue::Handle(f.try_clone()?);
        }
        StderrNull => {
            context.stderr = IoValue::Null;
        }
        StderrCapture => {
            context.stderr = IoValue::Handle(into_file(context.stderr_capture_pipe.try_clone()?));
        }
        StderrToStdout => {
            context.stderr = context.stdout.try_clone()?;
        }
        StdoutStderrSwap => {
            mem::swap(&mut context.stdout, &mut context.stderr);
        }
        Dir(p) => {
            context.dir = Some(p.clone());
        }
        Env(name, val) => {
            context.env.insert(name.clone(), val.clone());
        }
        EnvRemove(name) => {
            context.env.remove(name);
        }
        FullEnv(map) => {
            context.env = map.clone();
        }
        Unchecked => {
            let inner_handle = expr_inner.0.start(context)?;
            return Ok(HandleInner::Unchecked(Box::new(inner_handle)));
        }
        BeforeSpawn(hook) => {
            context.before_spawn_hooks.push(hook.clone());
        }
    }
    expr_inner.0.start(context)
}

#[derive(Debug)]
struct StdinBytesHandle {
    inner_handle: HandleInner,
    writer_thread: WriterThread,
}

impl StdinBytesHandle {
    fn start(
        expression: &Expression,
        mut context: IoContext,
        input: Arc<Vec<u8>>,
    ) -> io::Result<StdinBytesHandle> {
        let (reader, mut writer) = os_pipe::pipe()?;
        context.stdin = IoValue::Handle(into_file(reader));
        let inner = expression.0.start(context)?;
        // We only spawn the writer thread if the expression started
        // successfully, so that start errors won't leak a zombie thread.
        let thread = std::thread::spawn(move || writer.write_all(&input));
        Ok(StdinBytesHandle {
            inner_handle: inner,
            writer_thread: SharedThread::new(thread),
        })
    }

    fn wait(&self, mode: WaitMode) -> io::Result<Option<ExpressionStatus>> {
        // We're responsible for joining the writer thread and not leaving a zombie.
        // But waiting on the inner child can return an error, and in that case we
        // don't know whether the child is still running or not. The rule in
        // nonblocking mode is "clean up as much as we can, but never block," so we
        // can't wait on the writer thread. But the rule in blocking mode is "clean
        // up everything, even if some cleanup returns errors," so we must wait
        // regardless of what's going on with the child.
        let wait_res = self.inner_handle.wait(mode);
        if mode.should_join_background_thread(&wait_res) {
            // Join the writer thread. Broken pipe errors here are expected if
            // the child exited without reading all of its input, so we suppress
            // them. Return other errors though.
            match self.writer_thread.join() {
                Err(err) if err.kind() != io::ErrorKind::BrokenPipe => {
                    return Err(clone_io_error(err));
                }
                _ => {}
            }
        }
        wait_res
    }

    fn kill(&self) -> io::Result<()> {
        self.inner_handle.kill()
    }
}

#[derive(Debug)]
enum IoExpressionInner {
    StdinBytes(Arc<Vec<u8>>),
    StdinPath(PathBuf),
    StdinFile(File),
    StdinNull,
    StdoutPath(PathBuf),
    StdoutFile(File),
    StdoutNull,
    StdoutCapture,
    StdoutToStderr,
    StderrPath(PathBuf),
    StderrFile(File),
    StderrNull,
    StderrCapture,
    StderrToStdout,
    StdoutStderrSwap,
    Dir(PathBuf),
    Env(OsString, OsString),
    EnvRemove(OsString),
    FullEnv(HashMap<OsString, OsString>),
    Unchecked,
    BeforeSpawn(BeforeSpawnHook),
}

#[derive(Clone)]
struct BeforeSpawnHook {
    inner: Arc<dyn Fn(&mut Command) -> io::Result<()> + Send + Sync>,
}

impl BeforeSpawnHook {
    fn new<F>(hook: F) -> Self
    where
        F: Fn(&mut Command) -> io::Result<()> + Send + Sync + 'static,
    {
        Self {
            inner: Arc::new(hook),
        }
    }

    fn call(&self, command: &mut Command) -> io::Result<()> {
        (self.inner)(command)
    }
}

impl fmt::Debug for BeforeSpawnHook {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<closure>")
    }
}

// An IoContext represents the file descriptors child processes are talking to at execution time.
// It's initialized in run(), with dups of the stdin/stdout/stderr pipes, and then passed down to
// sub-expressions. Compound expressions will clone() it, and redirections will modify it.
#[derive(Debug)]
struct IoContext {
    stdin: IoValue,
    stdout: IoValue,
    stderr: IoValue,
    stdout_capture_pipe: os_pipe::PipeWriter,
    stderr_capture_pipe: os_pipe::PipeWriter,
    dir: Option<PathBuf>,
    env: HashMap<OsString, OsString>,
    before_spawn_hooks: Vec<BeforeSpawnHook>,
}

impl IoContext {
    // Returns (context, stdout_reader, stderr_reader).
    fn new() -> io::Result<(IoContext, ReaderThread, ReaderThread)> {
        let (stdout_capture_pipe, stdout_reader) = pipe_with_reader_thread()?;
        let (stderr_capture_pipe, stderr_reader) = pipe_with_reader_thread()?;
        let env: HashMap<_, _> = std::env::vars_os().collect();
        let context = IoContext {
            stdin: IoValue::ParentStdin,
            stdout: IoValue::ParentStdout,
            stderr: IoValue::ParentStderr,
            stdout_capture_pipe: stdout_capture_pipe,
            stderr_capture_pipe: stderr_capture_pipe,
            dir: None,
            env: env,
            before_spawn_hooks: Vec::new(),
        };
        Ok((context, stdout_reader, stderr_reader))
    }

    fn try_clone(&self) -> io::Result<IoContext> {
        Ok(IoContext {
            stdin: self.stdin.try_clone()?,
            stdout: self.stdout.try_clone()?,
            stderr: self.stderr.try_clone()?,
            stdout_capture_pipe: self.stdout_capture_pipe.try_clone()?,
            stderr_capture_pipe: self.stderr_capture_pipe.try_clone()?,
            dir: self.dir.clone(),
            env: self.env.clone(),
            before_spawn_hooks: self.before_spawn_hooks.clone(),
        })
    }
}

#[derive(Debug)]
enum IoValue {
    ParentStdin,
    ParentStdout,
    ParentStderr,
    Null,
    // We store all handles as File, even when they're e.g. anonymous pipes,
    // using the into_file() conversion below. The File type is a very thin
    // wrapper around the raw handle, but it gives us try_clone() and drop().
    Handle(File),
}

impl IoValue {
    fn try_clone(&self) -> io::Result<IoValue> {
        Ok(match self {
            IoValue::ParentStdin => IoValue::ParentStdin,
            IoValue::ParentStdout => IoValue::ParentStdout,
            IoValue::ParentStderr => IoValue::ParentStderr,
            IoValue::Null => IoValue::Null,
            IoValue::Handle(f) => IoValue::Handle(f.try_clone()?),
        })
    }

    fn into_stdio(self) -> io::Result<Stdio> {
        Ok(match self {
            IoValue::ParentStdin => os_pipe::dup_stdin()?.into(),
            IoValue::ParentStdout => os_pipe::dup_stdout()?.into(),
            IoValue::ParentStderr => os_pipe::dup_stderr()?.into(),
            IoValue::Null => Stdio::null(),
            IoValue::Handle(f) => f.into(),
        })
    }
}

// We would rather convert an fd-owning object directly into a
// std::process::Stdio, since all you can do with that is give it to a
// std::process::Command. Unfortunately, Stdio doesn't provide a try_clone
// method, and we need that in order to pass the object to multiple children.
// As a workaround, convert the object to a std::fs::File. All we will use this
// File for is try_clone and Into<Stdio>, which should be sound on any type of
// descriptor. (Some types will lead to an error, like a TcpStream, but that's
// not unsound.) If we discover any unsound cases, we might have to replace
// this with a new trait.
#[cfg(not(windows))]
fn into_file<T: IntoRawFd>(handle: T) -> File {
    unsafe { File::from_raw_fd(handle.into_raw_fd()) }
}
#[cfg(windows)]
fn into_file<T: IntoRawHandle>(handle: T) -> File {
    unsafe { File::from_raw_handle(handle.into_raw_handle()) }
}

// This struct keeps track of a child exit status, whether or not it's been
// unchecked(), and what the command was that gave it (for error messages).
#[derive(Clone, Debug)]
struct ExpressionStatus {
    status: ExitStatus,
    checked: bool,
    command: String,
}

impl ExpressionStatus {
    fn is_checked_error(&self) -> bool {
        self.checked && !self.status.success()
    }

    fn message(&self) -> String {
        format!(
            "command {} exited with code {}",
            self.command,
            self.exit_code_string()
        )
    }

    #[cfg(not(windows))]
    fn exit_code_string(&self) -> String {
        if self.status.code().is_none() {
            return format!("<signal {}>", self.status.signal().unwrap());
        }
        self.status.code().unwrap().to_string()
    }

    #[cfg(windows)]
    fn exit_code_string(&self) -> String {
        self.status.code().unwrap().to_string()
    }
}

fn canonicalize_exe_path_for_dir(exe_name: &OsStr, context: &IoContext) -> io::Result<OsString> {
    // There's a tricky interaction between exe paths and `dir`. Exe
    // paths can be relative, and so we have to ask: Is an exe path
    // interpreted relative to the parent's cwd, or the child's? The
    // answer is that it's platform dependent! >.< (Windows uses the
    // parent's cwd, but because of the fork-chdir-exec pattern, Unix
    // usually uses the child's.)
    //
    // We want to use the parent's cwd consistently, because that saves
    // the caller from having to worry about whether `dir` will have
    // side effects, and because it's easy for the caller to use
    // Path::join if they want to. That means that when `dir` is in use,
    // we need to detect exe names that are relative paths, and
    // absolutify them. We want to do that as little as possible though,
    // both because canonicalization can fail, and because we prefer to
    // let the caller control the child's argv[0].
    //
    // We never want to absolutify a name like "emacs", because that's
    // probably a program in the PATH rather than a local file. So we
    // look for slashes in the name to determine what's a filepath and
    // what isn't. Note that anything given as a std::path::Path will
    // always have a slash by the time we get here, because we
    // specialize the ToExecutable trait to prepend a ./ to them when
    // they're relative. This leaves the case where Windows users might
    // pass a local file like "foo.bat" as a string, which we can't
    // distinguish from a global program name. However, because the
    // Windows has the preferred "relative to parent's cwd" behavior
    // already, this case actually works without our help. (The thing
    // Windows users have to watch out for instead is local files
    // shadowing global program names, which I don't think we can or
    // should prevent.)

    let has_separator = exe_name
        .to_string_lossy()
        .chars()
        .any(std::path::is_separator);
    let is_relative = Path::new(exe_name).is_relative();
    if context.dir.is_some() && has_separator && is_relative {
        Path::new(exe_name).canonicalize().map(Into::into)
    } else {
        Ok(exe_name.to_owned())
    }
}

// We want to allow Path("foo") to refer to the local file "./foo" on
// Unix, and we want to *prevent* Path("echo") from referring to the
// global "echo" command on either Unix or Windows. Prepend a dot to all
// relative paths to accomplish both of those.
fn dotify_relative_exe_path(path: &Path) -> PathBuf {
    // This is a no-op if path is absolute or begins with a Windows prefix.
    Path::new(".").join(path)
}

/// An implementation detail of [`cmd`](fn.cmd.html), to distinguish paths from
/// other string types.
///
/// `Path("foo.sh")` means the file named `foo.sh` in the current directory.
/// However if you try to execute that path with
/// [`std::process::Command`](https://doc.rust-lang.org/std/process/struct.Command.html),
/// Unix will get upset that it doesn't have a leading `./`. Rust knows that the
/// string is a path, but that distinction gets lost by the time execution
/// happens.
///
/// To execute relative paths correctly, duct prepends the `./` to them
/// automatically. This trait captures the distinction between the path types
/// and other types of strings, which don't get modified. See the trait bounds
/// on [`cmd`](fn.cmd.html).
pub trait ToExecutable {
    fn to_executable(self) -> OsString;
}

// TODO: Get rid of most of these impls once specialization lands.

impl<'a> ToExecutable for &'a Path {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(self).into()
    }
}

impl ToExecutable for PathBuf {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(&self).into()
    }
}

impl<'a> ToExecutable for &'a PathBuf {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(self).into()
    }
}

impl<'a> ToExecutable for &'a str {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl ToExecutable for String {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl<'a> ToExecutable for &'a String {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl<'a> ToExecutable for &'a OsStr {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl ToExecutable for OsString {
    fn to_executable(self) -> OsString {
        self
    }
}

impl<'a> ToExecutable for &'a OsString {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

type ReaderThread = JoinHandle<io::Result<Vec<u8>>>;

fn pipe_with_reader_thread() -> io::Result<(os_pipe::PipeWriter, ReaderThread)> {
    let (mut reader, writer) = os_pipe::pipe()?;
    let thread = std::thread::spawn(move || {
        let mut output = Vec::new();
        reader.read_to_end(&mut output)?;
        Ok(output)
    });
    Ok((writer, thread))
}

type WriterThread = SharedThread<io::Result<()>>;

fn trim_end_newlines(s: &str) -> &str {
    s.trim_end_matches(|c| c == '\n' || c == '\r')
}

// io::Error doesn't implement clone directly, so we kind of hack it together.
fn clone_io_error(error: &io::Error) -> io::Error {
    if let Some(code) = error.raw_os_error() {
        io::Error::from_raw_os_error(code)
    } else {
        io::Error::new(error.kind(), error.to_string())
    }
}

#[derive(Debug)]
struct SharedThread<T> {
    result: OnceCell<T>,
    handle: Mutex<Option<JoinHandle<T>>>,
}

// A thread that sticks its result in a lazy cell, so that multiple callers can see it.
impl<T> SharedThread<T> {
    fn new(handle: JoinHandle<T>) -> Self {
        SharedThread {
            result: OnceCell::new(),
            handle: Mutex::new(Some(handle)),
        }
    }

    // If the other thread panicked, this will panic.
    fn join(&self) -> &T {
        let mut handle_lock = self.handle.lock().expect("shared thread handle poisoned");
        if let Some(handle) = handle_lock.take() {
            let ret = handle.join().expect("panic on shared thread");
            self.result
                .set(ret)
                .map_err(|_| "result lazycell unexpectedly full")
                .unwrap();
        }
        self.result
            .get()
            .expect("result lazycell unexpectedly empty")
    }
}

#[derive(Clone, Copy, Debug)]
enum WaitMode {
    Blocking,
    Nonblocking,
}

impl WaitMode {
    fn should_join_background_thread(
        &self,
        expression_result: &io::Result<Option<ExpressionStatus>>,
    ) -> bool {
        // Nonblocking waits can only join associated background threads if the
        // running expression is finished (that is, when the thread is
        // guaranteed to finish soon). Blocking waits should always join, even
        // in the presence of errors.
        if let WaitMode::Blocking = self {
            true
        } else if let Ok(Some(_)) = expression_result {
            true
        } else {
            false
        }
    }
}

#[cfg(windows)]
fn canonicalize_env_var_name(name: OsString) -> OsString {
    // On Windows, because env vars are case-insensitive, we uppercase all env
    // var names. That makes assignments and deletions in our internal map work
    // the same way they would on the real environment.
    match name.into_string() {
        Ok(name) => name.to_uppercase().into(),
        // If the name isn't valid Unicode then just leave it as is.
        Err(name) => name,
    }
}

#[cfg(not(windows))]
fn canonicalize_env_var_name(name: OsString) -> OsString {
    // No-op on all other platforms.
    name
}

#[cfg(test)]
mod test;
