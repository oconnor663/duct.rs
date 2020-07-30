//! Duct is a library for running child processes. Duct makes it easy to build
//! pipelines and redirect IO like a shell. At the same time, Duct helps you
//! write correct, portable code: whitespace is never significant, errors from
//! child processes get reported by default, and a variety of [gotchas, bugs,
//! and platform
//! inconsistencies](https://github.com/oconnor663/duct.py/blob/master/gotchas.md)
//! are handled for you the Right Way™.
//!
//! - [Documentation](https://docs.rs/duct)
//! - [Crate](https://crates.io/crates/duct)
//! - [GitHub repo](https://github.com/oconnor663/duct.rs)
//! - [the same library, in Python](https://github.com/oconnor663/duct.py)
//!
//! Examples
//! --------
//!
//! Run a command without capturing any output. Here "hi" is printed directly
//! to the terminal:
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! use duct::cmd;
//! cmd!("echo", "hi").run()?;
//! # }
//! # Ok(())
//! # }
//! ```
//!
//! Capture the standard output of a command. Here "hi" is returned as a
//! `String`:
//!
//! ```
//! # use duct::cmd;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! let stdout = cmd!("echo", "hi").read()?;
//! assert_eq!(stdout, "hi");
//! # }
//! # Ok(())
//! # }
//! ```
//!
//! Capture the standard output of a pipeline:
//!
//! ```
//! # use duct::cmd;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! let stdout = cmd!("echo", "hi").pipe(cmd!("sed", "s/i/o/")).read()?;
//! assert_eq!(stdout, "ho");
//! # }
//! # Ok(())
//! # }
//! ```
//!
//! Merge standard error into standard output and read both incrementally:
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! use duct::cmd;
//! use std::io::prelude::*;
//! use std::io::BufReader;
//!
//! let big_cmd = cmd!("bash", "-c", "echo out && echo err 1>&2");
//! let reader = big_cmd.stderr_to_stdout().reader()?;
//! let mut lines = BufReader::new(reader).lines();
//! assert_eq!(lines.next().unwrap()?, "out");
//! assert_eq!(lines.next().unwrap()?, "err");
//! # }
//! # Ok(())
//! # }
//! ```
//!
//! Children that exit with a non-zero status return an error by default:
//!
//! ```
//! # use duct::cmd;
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # if cfg!(not(windows)) {
//! let result = cmd!("false").run();
//! assert!(result.is_err());
//! let result = cmd!("false").unchecked().run();
//! assert!(result.is_ok());
//! # }
//! # Ok(())
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
pub fn cmd<T, U>(program: T, args: U) -> Expression
where
    T: IntoExecutablePath,
    U: IntoIterator,
    U::Item: Into<OsString>,
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

/// The central objects in Duct, Expressions are created with
/// [`cmd`](fn.cmd.html) or [`cmd!`](macro.cmd.html), combined with
/// [`pipe`](struct.Expression.html#method.pipe), and finally executed with
/// [`run`](struct.Expression.html#method.run),
/// [`read`](struct.Expression.html#method.read),
/// [`start`](struct.Expression.html#method.start), or
/// [`reader`](struct.Expression.html#method.reader). They also support several
/// methods to control their execution, like
/// [`stdin_bytes`](struct.Expression.html#method.stdin_bytes),
/// [`stdout_capture`](struct.Expression.html#method.stdout_capture),
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
#[derive(Clone)]
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
        // This could be optimized to avoid creating a background threads, by
        // using the current thread to read stdout or stderr if only one of
        // them is captured, or by using async IO to read both.
        self.start()?.into_output()
    }

    /// Execute an expression, capture its standard output, and return the
    /// captured output as a `String`. This is a convenience wrapper around
    /// [`reader`](struct.Expression.html#method.reader). Like backticks and
    /// `$()` in the shell, `read` trims trailing newlines.
    ///
    /// # Errors
    ///
    /// In addition to all the errors possible with
    /// [`run`](struct.Expression.html#method.run), `read` will return an error
    /// if the captured bytes aren't valid UTF-8.
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
        let mut reader = self.reader()?;
        let mut output = String::new();
        reader.read_to_string(&mut output)?;
        while output.ends_with('\n') || output.ends_with('\r') {
            output.truncate(output.len() - 1);
        }
        Ok(output)
    }

    /// Start running an expression, and immediately return a
    /// [`Handle`](struct.Handle.html) that represents all the child processes.
    /// This is analogous to the
    /// [`spawn`](https://doc.rust-lang.org/std/process/struct.Command.html#method.spawn)
    /// method in the standard library. The `Handle` may be shared between
    /// multiple threads.
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
        let stdout_capture = OutputCaptureContext::new();
        let stderr_capture = OutputCaptureContext::new();
        let context = IoContext::new(&stdout_capture, &stderr_capture);

        Ok(Handle {
            inner: self.0.start(context)?,
            result: OnceCell::new(),
            readers: Mutex::new((
                stdout_capture.maybe_read_thread(),
                stderr_capture.maybe_read_thread(),
            )),
        })
    }

    /// Start running an expression, and immediately return a
    /// [`ReaderHandle`](struct.ReaderHandle.html) attached to the child's
    /// stdout. This is similar to `.stdout_capture().start()`, but it returns
    /// the reader to the caller rather than reading from a background thread.
    ///
    /// Note that because this method doesn't read child output on a background
    /// thread, it's a best practice to only create one `ReaderHandle` at a
    /// time. Child processes with a lot of output will eventually block if
    /// their stdout pipe isn't read from. If you have multiple children
    /// running, but you're only reading from one of them at a time, that could
    /// block the others and lead to performance issues or deadlocks. For
    /// reading from multiple children at once, prefer
    /// `.stdout_capture().start()`.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::cmd;
    /// # use std::io::prelude::*;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let mut reader = cmd!("echo", "hi").reader().unwrap();
    /// let mut stdout = Vec::new();
    /// reader.read_to_end(&mut stdout).unwrap();
    /// assert_eq!(b"hi\n".to_vec(), stdout);
    /// # }
    /// # }
    /// ```
    pub fn reader(&self) -> io::Result<ReaderHandle> {
        let stdout_capture = OutputCaptureContext::new();
        let stderr_capture = OutputCaptureContext::new();
        let context = IoContext::new(&stdout_capture, &stderr_capture);
        let handle = Handle {
            inner: self.stdout_capture().0.start(context)?,
            result: OnceCell::new(),
            readers: Mutex::new((None, stderr_capture.maybe_read_thread())),
        };
        Ok(ReaderHandle {
            handle,
            reader: stdout_capture.pair.into_inner().expect("pipe opened").0,
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
    /// During spawning, if the left side of the pipe spawns successfully, but
    /// the right side fails to spawn, the left side will be killed and
    /// awaited. That's necessary to return the spawn error immediately,
    /// without leaking the left side as a zombie.
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

    /// Capture the standard output of an expression. The captured bytes will
    /// be available on the `stdout` field of the
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// object returned by [`run`](struct.Expression.html#method.run) or
    /// [`wait`](struct.Handle.html#method.wait). Output is read by a
    /// background thread, so the child will never block writing to stdout. But
    /// note that [`read`](struct.Expression.html#method.read) and
    /// [`reader`](struct.Expression.html#method.reader) can be more
    /// convenient, and they don't require the background thread.
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
    /// [`wait`](struct.Handle.html#method.wait). Output is read by a
    /// background thread, so the child will never block writing to stderr.
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
    /// Note that in some languages (Rust and Python at least), there are
    /// tricky platform differences in the way relative exe paths interact with
    /// child working directories. In particular, the exe path will be
    /// interpreted relative to the child dir on Unix, but relative to the
    /// parent dir on Windows. Duct prefers the Windows behavior, and in order
    /// to get that behavior on all platforms it calls
    /// [`std::fs::canonicalize`](https://doc.rust-lang.org/std/fs/fn.canonicalize.html)
    /// on relative exe paths when `dir` is in use. Paths in this sense are any
    /// program name containing a path separator, regardless of the type. (Note
    /// also that `Path` and `PathBuf` program names get a `./` prepended to
    /// them automatically by the
    /// [`IntoExecutablePath`](trait.IntoExecutablePath.html) trait, and so
    /// will always contain a separator.)
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

    /// Set the expression's entire environment, from a collection of
    /// name-value pairs (like a `HashMap`). Note that some environment
    /// variables are required for normal program execution (like `SystemRoot`
    /// on Windows), so copying the parent's environment is usually preferable
    /// to starting with an empty one.
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

// Delegate to the ExpressionInner for debug formatting. This avoids printing
// redundant Expression() constructors around everything.
impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
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
/// [`start`](struct.Expression.html#method.start) method.
///
/// Calling `start` followed by
/// [`into_output`](struct.Handle.html#method.into_output) on the handle is
/// equivalent to [`run`](struct.Expression.html#method.run). Note that unlike
/// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html),
/// most of the methods on `Handle` take `&self` rather than `&mut self`, and a
/// `Handle` may be shared between multiple threads.
///
/// Like `std::process::Child`, `Handle` doesn't do anything special in its
/// destructor. If you drop a handle without waiting on it, child processes and
/// background IO threads will keep running, and the children will become
/// [zombie processes](https://en.wikipedia.org/wiki/Zombie_process) when they
/// exit. That's a resource leak, similar to leaking memory or file handles.
/// Note that in contrast to `Handle`, a
/// [`ReaderHandle`](struct.ReaderHandle.html) kills child processes in its
/// destructor, to avoid creating zombies.
///
/// See the [`shared_child`](https://github.com/oconnor663/shared_child.rs)
/// crate for implementation details behind making handles thread safe.
#[derive(Debug)]
pub struct Handle {
    inner: HandleInner,
    result: OnceCell<(ExpressionStatus, Output)>,
    readers: Mutex<(Option<ReaderThread>, Option<ReaderThread>)>,
}

impl Handle {
    /// Wait for the running expression to finish, and return a reference to its
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html).
    /// Multiple threads may wait at the same time.
    ///
    /// # Errors
    ///
    /// In addition to all the IO errors possible with
    /// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html),
    /// `wait` will return an
    /// [`ErrorKind::Other`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html)
    /// IO error if child returns a non-zero exit status. To suppress this
    /// error and return an `Output` even when the exit status is non-zero, use
    /// the [`unchecked`](struct.Expression.html#method.unchecked) method.
    pub fn wait(&self) -> io::Result<&Output> {
        // Await the children and any threads that are reading their output.
        // Another caller may already have done this.
        let (expression_status, output) = wait_on_handle_and_ouput(self)?;
        // If the child returned a non-zero exit status, and that's a checked
        // error, return the error.
        if expression_status.is_checked_error() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                expression_status.message(),
            ));
        }
        Ok(output)
    }

    /// Check whether the running expression is finished. If it is, return a
    /// reference to its
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html).
    /// If it's still running, return `Ok(None)`.
    ///
    /// # Errors
    ///
    /// In addition to all the IO errors possible with
    /// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html),
    /// `try_wait` will return an
    /// [`ErrorKind::Other`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html)
    /// IO error if child returns a non-zero exit status. To suppress this
    /// error and return an `Output` even when the exit status is non-zero, use
    /// the [`unchecked`](struct.Expression.html#method.unchecked) method.
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
    ///
    /// # Errors
    ///
    /// In addition to all the IO errors possible with
    /// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html),
    /// `into_output` will return an
    /// [`ErrorKind::Other`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html)
    /// IO error if child returns a non-zero exit status. To suppress this
    /// error and return an `Output` even when the exit status is non-zero, use
    /// the [`unchecked`](struct.Expression.html#method.unchecked) method.
    pub fn into_output(self) -> io::Result<Output> {
        self.wait()?;
        let (_, output) = self.result.into_inner().expect("result missing");
        Ok(output)
    }

    /// Kill the running expression and await all the child processes. Any
    /// errors that would normally result from a non-zero exit status are
    /// ignored, as with
    /// [`unchecked`](struct.Expression.html#method.unchecked).
    ///
    /// Note that as with
    /// [`std::process::Child::kill`](https://doc.rust-lang.org/beta/std/process/struct.Child.html#method.kill),
    /// this does not kill any grandchild processes that the children have
    /// spawned on their own. It only kills the child processes that Duct
    /// spawned itself. See
    /// [`gotchas.md`](https://github.com/oconnor663/duct.py/blob/master/gotchas.md)
    /// for an extensive discussion of this behavior.
    pub fn kill(&self) -> io::Result<()> {
        self.inner.kill()?;
        // This wait cleans up the child but does not return an error for a
        // non-zero exit status.
        //
        // Note that we *must not* call wait_on_handle_and_ouput here. There
        // might be un-signaled grandchild processes holding the output pipe,
        // and we can't expect them to exit promptly. We only want to reap our
        // immediate zombie children here. See gotchas.md for more on why we
        // can't do better.
        self.inner.wait(WaitMode::Blocking)?;
        Ok(())
    }

    /// Return a `Vec<u32>` containing the PIDs of all of the child processes.
    /// The PIDs are given in pipeline order, from left to right.
    pub fn pids(&self) -> Vec<u32> {
        self.inner.pids()
    }
}

// Does a blocking wait on the handle, if it hasn't been awaited yet. This
// includes collection the output results from reader threads. After calling
// this function, the result cell is guaranteed to be populated. This does not
// do any status checking.
fn wait_on_handle_and_ouput(handle: &Handle) -> io::Result<&(ExpressionStatus, Output)> {
    // Take the reader threads lock and then see if a result has already been
    // collected. Doing this check inside the lock avoids racing to fill the
    // result if it's empty.
    let mut readers_lock = handle.readers.lock().expect("readers lock poisoned");
    if let Some(result) = handle.result.get() {
        // This handle has already been waited on. Return the same result
        // again.
        Ok(result)
    } else {
        // This handle hasn't been waited on yet. Do that now. If waiting on
        // the children returns an error, just short-circuit with that. This
        // shouldn't really happen.
        let status = handle
            .inner
            .wait(WaitMode::Blocking)?
            .expect("blocking wait can't return None");
        // Now that we have an exit status, we need to join the output reader
        // threads, if any. We're already holding the lock that we need.
        let (stdout_reader, stderr_reader) = &mut *readers_lock;
        // If either of the reader threads returned an error, just
        // short-circuit with that. Future calls to this function will panic.
        // But this really shouldn't happen.
        let stdout = stdout_reader
            .take()
            .map(|t| t.join().expect("stdout reader error"))
            .unwrap_or(Ok(Vec::new()))?;
        let stderr = stderr_reader
            .take()
            .map(|t| t.join().expect("stderr reader error"))
            .unwrap_or(Ok(Vec::new()))?;
        let output = Output {
            status: status.status,
            stdout,
            stderr,
        };
        Ok(handle.result.get_or_init(|| (status, output)))
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

    fn pids(&self) -> Vec<u32> {
        match self {
            HandleInner::Child(child_handle) => vec![child_handle.child.id()],
            HandleInner::Pipe(pipe_handle) => pipe_handle.pids(),
            HandleInner::StdinBytes(stdin_bytes_handle) => stdin_bytes_handle.inner_handle.pids(),
            HandleInner::Unchecked(inner_handle) => inner_handle.pids(),
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

    fn pids(&self) -> Vec<u32> {
        let mut pids = self.left_handle.pids();
        pids.extend_from_slice(&self.right_handle.pids());
        pids
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
            context.stdout = IoValue::Handle(into_file(context.stdout_capture.write_pipe()?));
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
            context.stderr = IoValue::Handle(into_file(context.stderr_capture.write_pipe()?));
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
    writer_thread: SharedThread<io::Result<()>>,
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
struct IoContext<'a> {
    stdin: IoValue,
    stdout: IoValue,
    stderr: IoValue,
    stdout_capture: &'a OutputCaptureContext,
    stderr_capture: &'a OutputCaptureContext,
    dir: Option<PathBuf>,
    env: HashMap<OsString, OsString>,
    before_spawn_hooks: Vec<BeforeSpawnHook>,
}

impl<'a> IoContext<'a> {
    // Returns (context, stdout_reader, stderr_reader).
    fn new(
        stdout_capture: &'a OutputCaptureContext,
        stderr_capture: &'a OutputCaptureContext,
    ) -> Self {
        Self {
            stdin: IoValue::ParentStdin,
            stdout: IoValue::ParentStdout,
            stderr: IoValue::ParentStderr,
            stdout_capture,
            stderr_capture,
            dir: None,
            env: std::env::vars_os().collect(),
            before_spawn_hooks: Vec::new(),
        }
    }

    fn try_clone(&self) -> io::Result<IoContext<'a>> {
        Ok(IoContext {
            stdin: self.stdin.try_clone()?,
            stdout: self.stdout.try_clone()?,
            stderr: self.stderr.try_clone()?,
            stdout_capture: self.stdout_capture,
            stderr_capture: self.stderr_capture,
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
    // There's a tricky interaction between exe paths and `dir`. Exe paths can
    // be relative, and so we have to ask: Is an exe path interpreted relative
    // to the parent's cwd, or the child's? The answer is that it's platform
    // dependent! >.< (Windows uses the parent's cwd, but because of the
    // fork-chdir-exec pattern, Unix usually uses the child's.)
    //
    // We want to use the parent's cwd consistently, because that saves the
    // caller from having to worry about whether `dir` will have side effects,
    // and because it's easy for the caller to use Path::join if they want to.
    // That means that when `dir` is in use, we need to detect exe names that
    // are relative paths, and absolutify them. We want to do that as little as
    // possible though, both because canonicalization can fail, and because we
    // prefer to let the caller control the child's argv[0].
    //
    // We never want to absolutify a name like "emacs", because that's probably
    // a program in the PATH rather than a local file. So we look for slashes
    // in the name to determine what's a filepath and what isn't. Note that
    // anything given as a std::path::Path will always have a slash by the time
    // we get here, because we specialize the IntoExecutablePath trait to
    // prepend a ./ to them when they're relative. This leaves the case where
    // Windows users might pass a local file like "foo.bat" as a string, which
    // we can't distinguish from a global program name. However, because the
    // Windows has the preferred "relative to parent's cwd" behavior already,
    // this case actually works without our help. (The thing Windows users have
    // to watch out for instead is local files shadowing global program names,
    // which I don't think we can or should prevent.)

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
pub trait IntoExecutablePath {
    fn to_executable(self) -> OsString;
}

// TODO: Get rid of most of these impls once specialization lands.

impl<'a> IntoExecutablePath for &'a Path {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(self).into()
    }
}

impl IntoExecutablePath for PathBuf {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(&self).into()
    }
}

impl<'a> IntoExecutablePath for &'a PathBuf {
    fn to_executable(self) -> OsString {
        dotify_relative_exe_path(self).into()
    }
}

impl<'a> IntoExecutablePath for &'a str {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl IntoExecutablePath for String {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl<'a> IntoExecutablePath for &'a String {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl<'a> IntoExecutablePath for &'a OsStr {
    fn to_executable(self) -> OsString {
        self.into()
    }
}

impl IntoExecutablePath for OsString {
    fn to_executable(self) -> OsString {
        self
    }
}

impl<'a> IntoExecutablePath for &'a OsString {
    fn to_executable(self) -> OsString {
        self.into()
    }
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
                .map_err(|_| "result cell unexpectedly full")
                .unwrap();
        }
        self.result.get().expect("result cell unexpectedly empty")
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

type ReaderThread = JoinHandle<io::Result<Vec<u8>>>;

#[derive(Debug)]
struct OutputCaptureContext {
    pair: OnceCell<(os_pipe::PipeReader, os_pipe::PipeWriter)>,
}

impl OutputCaptureContext {
    fn new() -> Self {
        Self {
            pair: OnceCell::new(),
        }
    }

    fn write_pipe(&self) -> io::Result<os_pipe::PipeWriter> {
        let (_, writer) = self.pair.get_or_try_init(|| os_pipe::pipe())?;
        writer.try_clone()
    }

    // Only spawn a read thread if the write pipe was used.
    fn maybe_read_thread(self) -> Option<ReaderThread> {
        if let Some((mut reader, _)) = self.pair.into_inner() {
            Some(std::thread::spawn(move || {
                let mut output = Vec::new();
                reader.read_to_end(&mut output)?;
                Ok(output)
            }))
        } else {
            None
        }
    }
}

/// An incremental reader created with the
/// [`Expression::reader`](struct.Expression.html#method.reader) method.
///
/// When this reader reaches EOF, it automatically calls
/// [`wait`](struct.Handle.html#method.wait) on the inner handle. If the child
/// returns a non-zero exit status, the read at EOF will return an error,
/// unless you use [`unchecked`](struct.Expression.html#method.unchecked).
///
/// If the reader is dropped before reaching EOF, it calls
/// [`kill`](struct.ReaderHandle.html#method.kill) in its destructor.
///
/// Both `ReaderHandle` and `&ReaderHandle` implement
/// [`std::io::Read`](https://doc.rust-lang.org/std/io/trait.Read.html). That
/// makes it possible for one thread to
/// [`kill`](struct.ReaderHandle.html#method.kill) the `ReaderHandle` while
/// another thread is reading it. That can be useful for effectively canceling
/// the read and unblocking the reader thread. However, note that killed child
/// processes return a non-zero exit status, which is an error for the reader
/// by default, unless you use
/// [`unchecked`](struct.Expression.html#method.unchecked).
///
/// # Example
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// # if cfg!(not(windows)) {
/// use duct::cmd;
/// use duct::ReaderHandle;
/// use std::sync::Arc;
/// use std::io::prelude::*;
///
/// // This child process prints a single byte and then sleeps.
/// //
/// // CAUTION: Using Bash for this example would probably hang, because Bash
/// // would spawn a `sleep` grandchild processes, and that grandchild wouldn't
/// // receive the kill signal.
/// let python_child = "\
/// import sys
/// import time
/// print()
/// sys.stdout.flush()
/// time.sleep(24 * 60 * 60)
/// ";
/// let reader: ReaderHandle = cmd!("python3", "-c", python_child)
///     .unchecked()
///     .reader()?;
///
/// // Spawn two threads that both try to read the single byte. Whichever one
/// // succeeds then calls kill() to unblock the other.
/// let arc_reader: Arc<ReaderHandle> = Arc::new(reader);
/// let mut threads = Vec::new();
/// for _ in 0..2 {
///     let arc_reader = arc_reader.clone();
///     threads.push(std::thread::spawn(move || -> std::io::Result<()> {
///         let mut single_byte = [0u8];
///         (&*arc_reader).read(&mut single_byte)?;
///         arc_reader.kill()?;
///         Ok(())
///     }));
/// }
///
/// // Join both threads. Because of the kill() above, both threads will exit
/// // quickly.
/// for thread in threads {
///     thread.join().unwrap()?;
/// }
/// # }
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct ReaderHandle {
    handle: Handle,
    reader: os_pipe::PipeReader,
}

impl ReaderHandle {
    /// Check whether the underlying expression is finished. This is equivalent
    /// to [`Handle::try_wait`](struct.Handle.html#method.try_wait). If the
    /// `ReaderHandle` has indicated EOF successfully, then it's guaranteed
    /// that this method will return `Ok(Some(_))`.
    ///
    /// Note that the
    /// [`stdout`](https://doc.rust-lang.org/std/process/struct.Output.html#structfield.stdout)
    /// field of the returned
    /// [`Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// will always be empty, because the `ReaderHandle` itself owns the
    /// child's stdout pipe.
    pub fn try_wait(&self) -> io::Result<Option<&Output>> {
        self.handle.try_wait()
    }

    /// Kill the underlying expression and await all the child processes.
    ///
    /// Any errors that would normally result from a non-zero exit status are
    /// ignored during this wait, as with
    /// [`Handle::kill`](struct.Handle.html#method.kill).
    ///
    /// Note that as with
    /// [`std::process::Child::kill`](https://doc.rust-lang.org/beta/std/process/struct.Child.html#method.kill),
    /// this does not kill any grandchild processes that the children have
    /// spawned on their own. It only kills the child processes that Duct
    /// spawned itself. This is **especially relevant** for `ReaderHandle`,
    /// because if you're using `kill` to unblock another thread that's
    /// reading, an unkilled grandchild process might keep the child's stdout
    /// pipe open and keep your reader thread blocked. For that use case, you
    /// need to ensure that any grandchild processes your child might spawn are
    /// going to be short-lived. See
    /// [`gotchas.md`](https://github.com/oconnor663/duct.py/blob/master/gotchas.md)
    /// for an extensive discussion of these issues.
    pub fn kill(&self) -> io::Result<()> {
        self.handle.kill()
    }

    /// Return a `Vec<u32>` containing the PIDs of all of the child processes.
    /// The PIDs are given in pipeline order, from left to right.
    pub fn pids(&self) -> Vec<u32> {
        self.handle.pids()
    }
}

impl<'a> Read for &'a ReaderHandle {
    /// Note that if you don't use
    /// [`unchecked`](struct.Expression.html#method.unchecked), and the child
    /// returns a non-zero exit status, the final call to `read` will return an
    /// error, just as [`run`](struct.Expression.html#method.run) would.
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = (&self.reader).read(buf)?;
        if n == 0 && buf.len() > 0 {
            // EOF detected. Wait on the child to clean it up before returning.
            self.handle.wait()?;
        }
        Ok(n)
    }
}

impl Read for ReaderHandle {
    /// Note that if you don't use
    /// [`unchecked`](struct.Expression.html#method.unchecked), and the child
    /// returns a non-zero exit status, the final call to `read` will return an
    /// error, just as [`run`](struct.Expression.html#method.run) would.
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        (&*self).read(buf)
    }
}

impl Drop for ReaderHandle {
    fn drop(&mut self) {
        // Just call kill() unconditionally. If wait() has already happened,
        // this has no effect.
        let _ = self.handle.kill();
    }
}

#[cfg(test)]
mod test;
