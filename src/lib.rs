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
//! # Example
//!
//! `duct` tries to be as concise as possible, so that you don't wish you were
//! back writing shell scripts. At the same time, it's explicit about what
//! happens to output, and strict about error codes in child processes.
//!
//! ```rust,no_run
//! #[macro_use]
//! extern crate duct;
//!
//! use duct::{cmd, sh};
//!
//! fn main() {
//!     // Read the name of the current git branch. If git exits with an error
//!     // code here (because we're not in a git repo, for example), `read` will
//!     // return an error too. `sh` commands run under the real system shell,
//!     // /bin/sh on Unix or cmd.exe on Windows.
//!     let current_branch = sh("git symbolic-ref --short HEAD").read().unwrap();
//!
//!     // Log the current branch, with git taking over the terminal as usual.
//!     // `cmd!` commands are spawned directly, without going through the
//!     // shell, so there aren't any escaping issues with variable arguments.
//!     cmd!("git", "log", current_branch).run().unwrap();
//!
//!     // More complicated expressions become trees. Here's a pipeline with two
//!     // child processes on the left, just because we can. In Bash this would
//!     // be: stdout=$((echo -n part one "" && echo part two) | sed s/p/sm/g)
//!     let part_one = &["-n", "part", "one", ""];
//!     let stdout = cmd("echo", part_one)
//!         .then(sh("echo part two"))
//!         .pipe(cmd!("sed", "s/p/sm/g"))
//!         .read()
//!         .unwrap();
//!     assert_eq!("smart one smart two", stdout);
//! }
//! ```
//!
//! `duct` uses [`os_pipe`](https://github.com/oconnor663/os_pipe.rs)
//! internally, and the docs for that one include a [big
//! example](https://docs.rs/os_pipe#example) that takes a dozen lines of code
//! to read both stdout and stderr from a child process. `duct` can do that in
//! one line:
//!
//! ```rust
//! use duct::sh;
//!
//! // This works on Windows too!
//! let output = sh("echo foo && echo bar >&2").stderr_to_stdout().read().unwrap();
//!
//! assert!(output.split_whitespace().eq(vec!["foo", "bar"]));
//! ```

extern crate os_pipe;

use os_pipe::FromFile;

use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio, Output, ExitStatus};
use std::thread::JoinHandle;
use std::sync::Arc;

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
    where T: ToExecutable,
          U: IntoIterator<Item = V>,
          V: Into<OsString>
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
/// #[macro_use]
/// extern crate duct;
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
    ( $program:expr ) => {
        {
            use std::ffi::OsString;
            use std::iter::empty;
            $crate::cmd($program, empty::<OsString>())
        }
    };
    ( $program:expr $(, $arg:expr )* ) => {
        {
            use std::ffi::OsString;
            let mut args: Vec<OsString> = Vec::new();
            $(
                args.push(Into::<OsString>::into($arg));
            )*
            $crate::cmd($program, args)
        }
    };
}

/// Create a command from a string of shell code.
///
/// This invokes the operating system's shell to execute the string:
/// `/bin/sh` on Unix-like systems and `cmd.exe` on Windows. This can be
/// very convenient sometimes, especially in small scripts and examples.
/// You don't need to quote each argument, and all the operators like
/// `|` and `>` work as usual.
///
/// However, building shell commands at runtime brings up tricky whitespace and
/// escaping issues, so avoid using `sh` and `format!` together. Prefer
/// [`cmd!`](macro.cmd.html) instead in those cases. Also note that shell
/// commands don't tend to be portable between Unix and Windows.
///
/// # Example
///
/// ```
/// use duct::sh;
///
/// let output = sh("echo foo bar baz").read();
///
/// assert_eq!("foo bar baz", output.unwrap());
/// ```
pub fn sh<T: ToExecutable>(command: T) -> Expression {
    Expression::new(Sh(command.to_executable()))
}

/// The central objects in `duct`, Expressions are created with
/// [`cmd`](fn.cmd.html), [`cmd!`](macro.cmd.html), or [`sh`](fn.sh.html), then
/// combined with [`pipe`](struct.Expression.html#method.pipe) or
/// [`then`](struct.Expression.html#method.then), and finally executed with
/// [`start`](struct.Expression.html#method.start),
/// [`run`](struct.Expression.html#method.run), or
/// [`read`](struct.Expression.html#method.read). They also support several
/// methods to control their execution, like
/// [`input`](struct.Expression.html#method.input),
/// [`env`](struct.Expression.html#method.env), and
/// [`unchecked`](struct.Expression.html#method.unchecked). Expressions are
/// immutable, and they do a lot of
/// [`Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html) sharing
/// internally, so all of these methods take `&self` and return a new
/// `Expression` cheaply.
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
    /// # #[macro_use] extern crate duct;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "hi").stdout_capture().run().unwrap();
    /// assert_eq!(b"hi\n".to_vec(), output.stdout);
    /// # }
    /// # }
    /// ```
    pub fn run(&self) -> io::Result<Output> {
        let (context, stdout_reader, stderr_reader) = IoContext::new()?;
        let status = self.0.exec(context)?;
        // These unwraps propagate any panics from the other thread,
        // but regular errors return normally.
        let stdout_vec = stdout_reader.join().unwrap()?;
        let stderr_vec = stderr_reader.join().unwrap()?;
        let output = Output {
            status: status.status,
            stdout: stdout_vec,
            stderr: stderr_vec,
        };
        if status.is_checked_error() {
            Err(io::Error::new(io::ErrorKind::Other, status.message()))
        } else {
            Ok(output)
        }
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
    /// # #[macro_use] extern crate duct;
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
            Ok(trim_right_newlines(output_str).to_owned())
        } else {
            Err(io::Error::new(io::ErrorKind::InvalidData, "stdout is not valid UTF-8"))
        }
    }

    /// Start running an expression, and immediately return a
    /// [`WaitHandle`](struct.WaitHandle.html). This is equivalent to
    /// [`run`](struct.Expression.html#method.run), except it doesn't block the
    /// current thread until you call
    /// [`wait`](struct.WaitHandle.html#method.wait) on the handle.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate duct;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let handle = cmd!("echo", "hi").stdout_capture().start();
    /// let output = handle.wait().unwrap();
    /// assert_eq!(b"hi\n".to_vec(), output.stdout);
    /// # }
    /// # }
    /// ```
    pub fn start(&self) -> WaitHandle {
        // Note that this returns a `WaitHandle` directly, not an
        // `io::Result<WaitHandle>`. That means that even IO errors that happen
        // during spawn (like a misspelled program name) won't show up until you
        // `wait` on the handle. The reason we can't report spawn errors
        // immediately is that it wouldn't work well with
        // [`then`](struct.Expression.html#method.then) and
        // [`pipe`](struct.Expression.html#method.pipe).
        //
        // The problem with `then` is that spawn errors in the right child don't
        // happen on the main thread. Instead there's a worker thread waiting on
        // the left child to finish, and it's that worker's job to spawn the
        // right child. The only way to return errors at that point is through
        // the WaitHandle, so a "return spawn errors immediately" design would
        // be inconsistent at best.
        //
        // The problem with `pipe` is worse. Both children start immediately, so
        // if a spawn error happens on the right, the left is already running.
        // Someone has to wait on it, or we'll leak a zombie process. But the
        // left child might take a long time to finish, and it's not ok for
        // `start` to block. Instead, we need the caller to `wait` as usual, so
        // that we can do this cleanup.
        //
        // Implementation note: This is currently implemented with a background
        // thread, so it's not as efficient as it could be.
        let clone = Expression(self.0.clone());
        WaitHandle(std::thread::spawn(move || clone.run()))
    }

    /// Join two expressions into a pipe, with the standard output of the left
    /// hooked up to the standard input of the right, like `|` in the shell. If
    /// either side of the pipe returns a non-zero exit status, that becomes the
    /// status of the whole pipe, similar to Bash's `pipefail` option. If both
    /// sides return non-zero, and one of them is
    /// [`unchecked`](struct.Expression.html#method.unchecked), then the checked
    /// side wins. Otherwise the right side wins.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate duct;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("echo", "hi").pipe(cmd!("sed", "s/h/p/")).read();
    /// assert_eq!("pi", output.unwrap());
    /// # }
    /// # }
    /// ```
    pub fn pipe(&self, right: Expression) -> Expression {
        Self::new(Pipe(self.clone(), right.clone()))
    }

    /// Chain two expressions together to run in series, like `&&` in the shell.
    /// If the left child returns a non-zero exit status, the right child
    /// doesn't run. (You can use
    /// [`unchecked`](struct.Expression.html#method.unchecked) on the left child
    /// to make sure the right child always runs.) The exit status of this
    /// expression is the status of the last child that ran.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate duct;
    /// # use duct::sh;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // Both echoes share the same stdout, so both go through `sed`.
    /// # // NOTE: The shell's builtin echo doesn't support -n on OSX.
    /// let output = cmd!("echo", "-n", "bar")
    ///     .then(sh("echo baz"))
    ///     .pipe(sh("sed s/b/f/g")).read();
    /// assert_eq!("farfaz", output.unwrap());
    /// # }
    /// # }
    /// ```
    pub fn then(&self, right: Expression) -> Expression {
        Self::new(Then(self.clone(), right.clone()))
    }

    /// Use bytes or a string as input for an expression, like `<<<` in the
    /// shell. A worker thread will be spawned at runtime to write this input.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate duct;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<Vec<u8>>. Here's a string.
    /// let output = cmd!("cat").input("foo").read().unwrap();
    /// assert_eq!("foo", output);
    ///
    /// // And here's a byte slice.
    /// let output = cmd!("cat").input(&b"foo"[..]).read().unwrap();
    /// assert_eq!("foo", output);
    /// # }
    /// # }
    /// ```
    pub fn input<T: Into<Vec<u8>>>(&self, input: T) -> Self {
        Self::new(Io(Input(Arc::new(input.into())), self.clone()))
    }

    /// Open a file at the given path and use it as input for an expression, like
    /// `<` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let output = sh("head -c 3").stdin("/dev/zero").read().unwrap();
    /// assert_eq!("\0\0\0", output);
    /// # }
    /// ```
    pub fn stdin<T: Into<PathBuf>>(&self, path: T) -> Self {
        Self::new(Io(Stdin(path.into()), self.clone()))
    }

    /// Use an already opened file as input for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # if cfg!(not(windows)) {
    /// let input_file = std::fs::File::open("/dev/zero").unwrap();
    /// let output = sh("head -c 3").stdin_file(input_file).read().unwrap();
    /// assert_eq!("\0\0\0", output);
    /// # }
    /// ```
    pub fn stdin_file(&self, file: File) -> Self {
        Self::new(Io(StdinFile(file), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as input for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate duct;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("cat").stdin_null().read().unwrap();
    /// assert_eq!("", output);
    /// # }
    /// # }
    /// ```
    pub fn stdin_null(&self) -> Self {
        Self::new(Io(StdinNull, self.clone()))
    }

    /// Open a file at the given path and use it as output for an expression,
    /// like `>` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let path = "/tmp/duct_test_tmp.txt";
    /// sh("echo wee").stdout(path).run().unwrap();
    /// let mut output = String::new();
    /// std::fs::File::open(path).unwrap().read_to_string(&mut output).unwrap();
    /// assert_eq!("wee\n", output);
    /// # }
    /// ```
    pub fn stdout<T: Into<PathBuf>>(&self, path: T) -> Self {
        Self::new(Io(Stdout(path.into()), self.clone()))
    }

    /// Use an already opened file as output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// let path = "/tmp/duct_test_tmp.txt";
    /// let file = std::fs::File::create(path).unwrap();
    /// sh("echo wee").stdout_file(file).run().unwrap();
    /// let mut output = String::new();
    /// std::fs::File::open(path).unwrap().read_to_string(&mut output).unwrap();
    /// assert_eq!("wee\n", output);
    /// # }
    /// ```
    pub fn stdout_file(&self, file: File) -> Self {
        Self::new(Io(StdoutFile(file), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// // This echo command won't print anything.
    /// sh("echo foo bar baz").stdout_null().run().unwrap();
    ///
    /// // And you won't get anything even if you try to read its output! The
    /// // null redirect happens farther down in the expression tree than the
    /// // implicit `stdout_capture`, and so it takes precedence.
    /// let output = sh("echo foo bar baz").stdout_null().read().unwrap();
    /// assert_eq!("", output);
    /// ```
    pub fn stdout_null(&self) -> Self {
        Self::new(Io(StdoutNull, self.clone()))
    }

    /// Capture the standard output of an expression. The captured bytes will be
    /// available on the `stdout` field of the
    /// [`std::process::Output`](https://doc.rust-lang.org/std/process/struct.Output.html)
    /// object returned by [`run`](struct.Expression.html#method.run) or
    /// [`wait`](struct.WaitHandle.html#method.wait). In the simplest cases,
    /// [`read`](struct.Expression.html#method.read) can be more convenient.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # if cfg!(not(windows)) {
    /// // The most direct way to read stdout bytes is `stdout_capture`.
    /// let output1 = sh("echo foo").stdout_capture().run().unwrap().stdout;
    /// assert_eq!(&b"foo\n"[..], &output1[..]);
    ///
    /// // The `read` method is a shorthand for `stdout_capture`, and it also
    /// // does string parsing and newline trimming.
    /// let output2 = sh("echo foo").read().unwrap();
    /// assert_eq!("foo", output2)
    /// # }
    /// ```
    pub fn stdout_capture(&self) -> Self {
        Self::new(Io(StdoutCapture, self.clone()))
    }

    /// Join the standard output of an expression to its standard error pipe,
    /// similar to `1>&2` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # if cfg!(not(windows)) {
    /// let output = sh("echo foo").stdout_to_stderr().stderr_capture().run().unwrap();
    /// assert_eq!(&b"foo\n"[..], &output.stderr[..]);
    /// # }
    /// ```
    pub fn stdout_to_stderr(&self) -> Self {
        Self::new(Io(StdoutToStderr, self.clone()))
    }

    /// Open a file at the given path and use it as error output for an
    /// expression, like `2>` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// // Many types implement Into<PathBuf>, including &str.
    /// let path = "/tmp/duct_test_tmp.txt";
    /// sh("echo wee >&2").stderr(path).run().unwrap();
    /// let mut error_output = String::new();
    /// std::fs::File::open(path).unwrap().read_to_string(&mut error_output).unwrap();
    /// assert_eq!("wee\n", error_output);
    /// # }
    /// ```
    pub fn stderr<T: Into<PathBuf>>(&self, path: T) -> Self {
        Self::new(Io(Stderr(path.into()), self.clone()))
    }

    /// Use an already opened file as error output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # use std::io::prelude::*;
    /// # if cfg!(not(windows)) {
    /// let path = "/tmp/duct_test_tmp.txt";
    /// let file = std::fs::File::create(path).unwrap();
    /// sh("echo wee >&2").stderr_file(file).run().unwrap();
    /// let mut error_output = String::new();
    /// std::fs::File::open(path).unwrap().read_to_string(&mut error_output).unwrap();
    /// assert_eq!("wee\n", error_output);
    /// # }
    /// ```
    pub fn stderr_file(&self, file: File) -> Self {
        Self::new(Io(StderrFile(file.into()), self.clone()))
    }

    /// Use `/dev/null` (or `NUL` on Windows) as error output for an expression.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// // This echo-to-stderr command won't print anything.
    /// sh("echo foo bar baz >&2").stderr_null().run().unwrap();
    /// ```
    pub fn stderr_null(&self) -> Self {
        Self::new(Io(StderrNull, self.clone()))
    }

    /// Capture the error output of an expression. The captured bytes will be
    /// available on the `stderr` field of the `Output` object returned by
    /// [`run`](struct.Expression.html#method.run) or
    /// [`wait`](struct.WaitHandle.html#method.wait).
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # if cfg!(not(windows)) {
    /// let output_obj = sh("echo foo >&2").stderr_capture().run().unwrap();
    /// assert_eq!(&b"foo\n"[..], &output_obj.stderr[..]);
    /// # }
    /// ```
    pub fn stderr_capture(&self) -> Self {
        Self::new(Io(StderrCapture, self.clone()))
    }

    /// Join the standard error of an expression to its standard output pipe,
    /// similar to `2>&1` in the shell.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # if cfg!(not(windows)) {
    /// let error_output = sh("echo foo >&2").stderr_to_stdout().read().unwrap();
    /// assert_eq!("foo", error_output);
    /// # }
    /// ```
    pub fn stderr_to_stdout(&self) -> Self {
        Self::new(Io(StderrToStdout, self.clone()))
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
    /// # #[macro_use] extern crate duct;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// let output = cmd!("pwd").dir("/").read().unwrap();
    /// assert_eq!("/", output);
    /// # }
    /// # }
    /// ```
    pub fn dir<T: Into<PathBuf>>(&self, path: T) -> Self {
        Self::new(Io(Dir(path.into()), self.clone()))
    }

    /// Set a variable in the expression's environment.
    ///
    /// # Example
    ///
    /// ```
    /// # use duct::sh;
    /// # if cfg!(not(windows)) {
    /// let output = sh("echo $FOO").env("FOO", "bar").read().unwrap();
    /// assert_eq!("bar", output);
    /// # }
    /// ```
    pub fn env<T, U>(&self, name: T, val: U) -> Self
        where T: Into<OsString>,
              U: Into<OsString>
    {
        Self::new(Io(Env(name.into(), val.into()), self.clone()))
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
    /// # use duct::sh;
    /// # use std::collections::HashMap;
    /// # if cfg!(not(windows)) {
    /// let mut env_map: HashMap<_, _> = std::env::vars().collect();
    /// env_map.insert("FOO".into(), "bar".into());
    /// let output = sh("echo $FOO").full_env(env_map).read().unwrap();
    /// assert_eq!("bar", output);
    ///
    /// // The IntoIterator/Into<OsString> bounds are pretty flexible. A shared
    /// // reference works here too.
    /// # let mut env_map: HashMap<_, _> = std::env::vars().collect();
    /// # env_map.insert("FOO".into(), "bar".into());
    /// let output = sh("echo $FOO").full_env(&env_map).read().unwrap();
    /// assert_eq!("bar", output);
    /// # }
    /// ```
    pub fn full_env<T, U, V>(&self, name_vals: T) -> Self
        where T: IntoIterator<Item = (U, V)>,
              U: Into<OsString>,
              V: Into<OsString>
    {
        let env_map = name_vals.into_iter()
            .map(|(k, v)| (k.into(), v.into()))
            .collect();
        Self::new(Io(FullEnv(env_map), self.clone()))
    }

    /// Prevent a non-zero exit status from short-circuiting a
    /// [`then`](struct.Expression.html#method.then) expression or from causing
    /// [`run`](struct.Expression.html#method.run) and friends to return an
    /// error. The unchecked exit code will still be there on the `Output`
    /// returned by `run`; its value doesn't change.
    ///
    /// "Uncheckedness" sticks to an exit code as it bubbles up through
    /// complicated expressions, but it doesn't "infect" other exit codes. So
    /// for example, if only one sub-expression in a pipe has `unchecked`, then
    /// errors returned by the other side will still be checked. That said,
    /// most commonly you'll just call `unchecked` right before `run`, and it'll
    /// apply to an entire expression. This sub-expression stuff doesn't usually
    /// come up unless you have a big pipeline built out of lots of different
    /// pieces.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate duct;
    /// # fn main() {
    /// # if cfg!(not(windows)) {
    /// // Normally the `false` command (which does nothing but return a
    /// // non-zero exit status) would short-circuit the `then` expression and
    /// // also make `read` return an error. `unchecked` prevents this.
    /// cmd!("false").unchecked().then(cmd!("echo", "hi")).read().unwrap();
    /// # }
    /// # }
    /// ```
    pub fn unchecked(&self) -> Self {
        Self::new(Io(Unchecked, self.clone()))
    }

    fn new(inner: ExpressionInner) -> Self {
        Expression(Arc::new(inner))
    }
}

/// Returned by the [`start`](struct.Expression.html#method.start) method.
/// Calling `start` followed by [`wait`](struct.WaitHandle.html#method.wait) on
/// the handle is equivalent to [`run`](struct.Expression.html#method.run).
pub struct WaitHandle(JoinHandle<io::Result<Output>>);

impl WaitHandle {
    /// Wait for the running expression to finish, and return its output.
    /// Calling `start` followed by [`wait`](struct.WaitHandle.html#method.wait)
    /// is equivalent to [`run`](struct.Expression.html#method.run).
    pub fn wait(self) -> io::Result<Output> {
        self.0.join().unwrap()
    }
}

#[derive(Debug)]
enum ExpressionInner {
    Cmd(Vec<OsString>),
    Sh(OsString),
    Pipe(Expression, Expression),
    Then(Expression, Expression),
    Io(IoExpressionInner, Expression),
}

impl ExpressionInner {
    fn exec(&self, context: IoContext) -> io::Result<ExpressionStatus> {
        match *self {
            Cmd(ref argv) => exec_argv(argv, context),
            Sh(ref command) => exec_sh(command, context),
            Pipe(ref left, ref right) => exec_pipe(left, right, context),
            Then(ref left, ref right) => exec_then(left, right, context),
            Io(ref io_inner, ref expr) => exec_io(io_inner, expr, context),
        }
    }
}

fn maybe_canonicalize_exe_path(exe_name: &OsStr, context: &IoContext) -> io::Result<OsString> {
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

    let has_separator = exe_name.to_string_lossy().chars().any(std::path::is_separator);
    let is_relative = Path::new(exe_name).is_relative();
    if context.dir.is_some() && has_separator && is_relative {
        Path::new(exe_name).canonicalize().map(Into::into)
    } else {
        Ok(exe_name.to_owned())
    }
}

fn exec_argv(argv: &[OsString], context: IoContext) -> io::Result<ExpressionStatus> {
    let exe = maybe_canonicalize_exe_path(&argv[0], &context)?;
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
    Ok(ExpressionStatus {
        status: command.status()?,
        checked: true,
        command: format!("{:?}", argv),
    })
}

#[cfg(unix)]
fn shell_command_argv(command: OsString) -> [OsString; 3] {
    [OsStr::new("/bin/sh").to_owned(), OsStr::new("-c").to_owned(), command]
}

#[cfg(windows)]
fn shell_command_argv(command: OsString) -> [OsString; 3] {
    let comspec = std::env::var_os("COMSPEC").unwrap_or(OsStr::new("cmd.exe").to_owned());
    [comspec, OsStr::new("/C").to_owned(), command]
}

fn exec_sh(command: &OsString, context: IoContext) -> io::Result<ExpressionStatus> {
    exec_argv(&shell_command_argv(command.clone()), context)
}

fn exec_pipe(left: &Expression,
             right: &Expression,
             context: IoContext)
             -> io::Result<ExpressionStatus> {
    let (reader, writer) = os_pipe::pipe()?;
    let mut left_context = context.try_clone()?; // dup'ing stdin/stdout isn't strictly necessary, but no big deal
    left_context.stdout = IoValue::File(File::from_file(writer));
    let mut right_context = context;
    right_context.stdin = IoValue::File(File::from_file(reader));

    let left_clone = Expression(left.0.clone());
    let left_joiner = std::thread::spawn(move || left_clone.0.exec(left_context));
    let right_result = right.0.exec(right_context);
    let left_result = left_joiner.join().unwrap();

    // First return any IO errors, with the right side taking precedence.
    let right_status = right_result?;
    let left_status = left_result?;

    // Now return one of the two statuses. The rules of precedence are:
    // 1) Checked errors trump unchecked errors.
    // 2) Unchecked errors trump success.
    // 3) All else equal, right side wins.
    Ok(if right_status.is_checked_error() {
        right_status
    } else if left_status.is_checked_error() {
        left_status
    } else if !right_status.status.success() {
        right_status
    } else {
        left_status
    })
}

fn exec_then(left: &Expression,
             right: &Expression,
             context: IoContext)
             -> io::Result<ExpressionStatus> {
    let status = left.0.exec(context.try_clone()?)?;
    if status.is_checked_error() {
        // Checked status errors are `Ok` because they're not literally IO
        // errors, but we short circuit and bubble them up.
        Ok(status)
    } else {
        right.0.exec(context)
    }
}

fn exec_io(io_inner: &IoExpressionInner,
           expr: &Expression,
           context: IoContext)
           -> io::Result<ExpressionStatus> {
    {
        let (new_context, maybe_writer_thread) = io_inner.update_context(context)?;
        let exec_result = expr.0.exec(new_context);
        let writer_result = join_maybe_writer_thread(maybe_writer_thread);
        // Propagate any exec errors first.
        let mut exec_status = exec_result?;
        // Then propagate any writer thread errors.
        writer_result?;
        // Finally, implement unchecked() status suppression here.
        if let &Unchecked = io_inner {
            exec_status.checked = false;
        }
        Ok(exec_status)
    }
}

#[derive(Debug)]
enum IoExpressionInner {
    Input(Arc<Vec<u8>>),
    Stdin(PathBuf),
    StdinFile(File),
    StdinNull,
    Stdout(PathBuf),
    StdoutFile(File),
    StdoutNull,
    StdoutCapture,
    StdoutToStderr,
    Stderr(PathBuf),
    StderrFile(File),
    StderrNull,
    StderrCapture,
    StderrToStdout,
    Dir(PathBuf),
    Env(OsString, OsString),
    FullEnv(HashMap<OsString, OsString>),
    Unchecked,
}

impl IoExpressionInner {
    fn update_context(&self,
                      mut context: IoContext)
                      -> io::Result<(IoContext, Option<WriterThread>)> {
        let mut maybe_thread = None;
        match *self {
            Input(ref v) => {
                let (reader, thread) = pipe_with_writer_thread(v)?;
                context.stdin = IoValue::File(reader);
                maybe_thread = Some(thread)
            }
            Stdin(ref p) => {
                context.stdin = IoValue::File(File::open(p)?);
            }
            StdinFile(ref f) => {
                context.stdin = IoValue::File(f.try_clone()?);
            }
            StdinNull => {
                context.stdin = IoValue::Null;
            }
            Stdout(ref p) => {
                context.stdout = IoValue::File(File::create(p)?);
            }
            StdoutFile(ref f) => {
                context.stdout = IoValue::File(f.try_clone()?);
            }
            StdoutNull => {
                context.stdout = IoValue::Null;
            }
            StdoutCapture => context.stdout = IoValue::File(context.stdout_capture.try_clone()?),
            StdoutToStderr => {
                context.stdout = context.stderr.try_clone()?;
            }
            Stderr(ref p) => {
                context.stderr = IoValue::File(File::create(p)?);
            }
            StderrFile(ref f) => {
                context.stderr = IoValue::File(f.try_clone()?);
            }
            StderrNull => {
                context.stderr = IoValue::Null;
            }
            StderrCapture => context.stderr = IoValue::File(context.stderr_capture.try_clone()?),
            StderrToStdout => {
                context.stderr = context.stdout.try_clone()?;
            }
            Dir(ref p) => {
                context.dir = Some(p.clone());
            }
            Env(ref name, ref val) => {
                context.env.insert(name.clone(), val.clone());
            }
            FullEnv(ref map) => {
                context.env = map.clone();
            }
            Unchecked => {
                // No-op. Unchecked is handled in exec_io().
            }
        }
        Ok((context, maybe_thread))
    }
}

// We want to allow Path("foo") to refer to the local file "./foo" on
// Unix, and we want to *prevent* Path("echo") from referring to the
// global "echo" command on either Unix or Windows. Prepend a dot to all
// relative paths to accomplish both of those.
fn sanitize_exe_path<T: Into<PathBuf>>(path: T) -> PathBuf {
    let path_buf = path.into();
    // Don't try to be too clever with checking parent(). The parent of "foo" is
    // Some(""). See https://github.com/rust-lang/rust/issues/36861. Also we
    // don't strictly need the has_root check, because joining a leading dot is
    // a no-op in that case, but explicitly checking it is clearer.
    if path_buf.is_absolute() || path_buf.has_root() {
        path_buf
    } else {
        Path::new(".").join(path_buf)
    }
}

/// `duct` provides several impls of this trait to handle the difference between
/// [`Path`](https://doc.rust-lang.org/std/path/struct.Path.html)/[`PathBuf`](https://doc.rust-lang.org/std/path/struct.PathBuf.html)
/// and other types of strings. In particular, `duct` automatically prepends a
/// leading dot to relative paths (though not other string types) before
/// executing them. This is required for single-component relative paths to work
/// at all on Unix, and it prevents aliasing with programs in the global `PATH`
/// on both Unix and Windows. See the trait bounds on [`cmd`](fn.cmd.html) and
/// [`sh`](fn.sh.html).
pub trait ToExecutable {
    fn to_executable(self) -> OsString;
}

// TODO: Get rid of most of these impls once specialization lands.

impl<'a> ToExecutable for &'a Path {
    fn to_executable(self) -> OsString {
        sanitize_exe_path(self).into()
    }
}

impl ToExecutable for PathBuf {
    fn to_executable(self) -> OsString {
        sanitize_exe_path(self).into()
    }
}

impl<'a> ToExecutable for &'a PathBuf {
    fn to_executable(self) -> OsString {
        sanitize_exe_path(&**self).into()
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

// An IoContext represents the file descriptors child processes are talking to at execution time.
// It's initialized in run(), with dups of the stdin/stdout/stderr pipes, and then passed down to
// sub-expressions. Compound expressions will clone() it, and redirections will modify it.
#[derive(Debug)]
struct IoContext {
    stdin: IoValue,
    stdout: IoValue,
    stderr: IoValue,
    stdout_capture: File,
    stderr_capture: File,
    dir: Option<PathBuf>,
    env: HashMap<OsString, OsString>,
}

impl IoContext {
    // Returns (context, stdout_reader, stderr_reader).
    fn new() -> io::Result<(IoContext, ReaderThread, ReaderThread)> {
        let (stdout_capture, stdout_reader) = pipe_with_reader_thread()?;
        let (stderr_capture, stderr_reader) = pipe_with_reader_thread()?;
        let mut env = HashMap::new();
        for (name, val) in std::env::vars_os() {
            env.insert(name, val);
        }
        let context = IoContext {
            stdin: IoValue::ParentStdin,
            stdout: IoValue::ParentStdout,
            stderr: IoValue::ParentStderr,
            stdout_capture: stdout_capture,
            stderr_capture: stderr_capture,
            dir: None,
            env: env,
        };
        Ok((context, stdout_reader, stderr_reader))
    }

    fn try_clone(&self) -> io::Result<IoContext> {
        Ok(IoContext {
            stdin: self.stdin.try_clone()?,
            stdout: self.stdout.try_clone()?,
            stderr: self.stderr.try_clone()?,
            stdout_capture: self.stdout_capture.try_clone()?,
            stderr_capture: self.stderr_capture.try_clone()?,
            dir: self.dir.clone(),
            env: self.env.clone(),
        })
    }
}

#[derive(Debug)]
enum IoValue {
    ParentStdin,
    ParentStdout,
    ParentStderr,
    Null,
    File(File),
}

impl IoValue {
    fn try_clone(&self) -> io::Result<IoValue> {
        Ok(match self {
            &IoValue::ParentStdin => IoValue::ParentStdin,
            &IoValue::ParentStdout => IoValue::ParentStdout,
            &IoValue::ParentStderr => IoValue::ParentStderr,
            &IoValue::Null => IoValue::Null,
            &IoValue::File(ref f) => IoValue::File(f.try_clone()?),
        })
    }

    fn into_stdio(self) -> io::Result<Stdio> {
        match self {
            IoValue::ParentStdin => os_pipe::parent_stdin(),
            IoValue::ParentStdout => os_pipe::parent_stdout(),
            IoValue::ParentStderr => os_pipe::parent_stderr(),
            IoValue::Null => Ok(Stdio::null()),
            IoValue::File(f) => Ok(Stdio::from_file(f)),
        }
    }
}

type ReaderThread = JoinHandle<io::Result<Vec<u8>>>;

fn pipe_with_reader_thread() -> io::Result<(File, ReaderThread)> {
    let (mut reader, writer) = os_pipe::pipe()?;
    let thread = std::thread::spawn(move || {
        let mut output = Vec::new();
        reader.read_to_end(&mut output)?;
        Ok(output)
    });
    Ok((File::from_file(writer), thread))
}

type WriterThread = JoinHandle<io::Result<()>>;

fn pipe_with_writer_thread(input: &Arc<Vec<u8>>) -> io::Result<(File, WriterThread)> {
    let (reader, mut writer) = os_pipe::pipe()?;
    let new_arc = input.clone();
    let thread = std::thread::spawn(move || {
        writer.write_all(&new_arc)?;
        Ok(())
    });
    Ok((File::from_file(reader), thread))
}

fn join_maybe_writer_thread(maybe_writer_thread: Option<WriterThread>) -> io::Result<()> {
    if let Some(thread) = maybe_writer_thread {
        // A broken pipe error happens if the process on the other end exits before
        // we're done writing. We ignore those but return any other errors to the
        // caller.
        suppress_broken_pipe_errors(thread.join().unwrap())
    } else {
        Ok(())
    }
}

// This is split out to make it easier to get test coverage.
fn suppress_broken_pipe_errors(r: io::Result<()>) -> io::Result<()> {
    if let &Err(ref io_error) = &r {
        if io_error.kind() == io::ErrorKind::BrokenPipe {
            return Ok(());
        }
    }
    r
}

fn trim_right_newlines(s: &str) -> &str {
    s.trim_right_matches(|c| c == '\n' || c == '\r')
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
        format!("command {} exited with code {}",
                self.command,
                self.exit_code_string())
    }

    #[cfg(not(windows))]
    fn exit_code_string(&self) -> String {
        use std::os::unix::process::ExitStatusExt;
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

#[cfg(test)]
mod test;
