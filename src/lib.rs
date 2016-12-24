//! A cross-platform library for running child processes and building
//! pipelines.
//!
//! `duct` wants to make shelling out in Rust as easy and flexible as it
//! is in Bash. It also takes care of [tricky
//! inconsistencies](https://github.com/oconnor663/duct.py/blob/master/spec.md#consistent-behavior-for-dir)
//! in the way different platforms shell out. And it's a cross-language
//! library; the [original
//! implementation](https://github.com/oconnor663/duct.py) is in Python,
//! with an identical API.
//!
//! - [Docs](https://docs.rs/duct)
//! - [Crate](https://crates.io/crates/duct)
//! - [Repo](https://github.com/oconnor663/duct.rs)
//!
//! # Example
//!
//! `duct` uses [`os_pipe`](https://github.com/oconnor663/os_pipe.rs)
//! internally, and the docs for that one include a [big
//! example](https://docs.rs/os_pipe#example) that uses more than a
//! dozen lines of code to read both stdout and stderr from a child
//! process. `duct` can do that in one line:
//!
//! ```rust
//! use duct::sh;
//!
//! let output = sh("echo foo && echo bar >&2").stderr_to_stdout().read().unwrap();
//!
//! assert!(output.split_whitespace().eq(vec!["foo", "bar"]));
//! ```

extern crate crossbeam;
extern crate os_pipe;

use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fs::File;
use std::io;
use std::io::prelude::*;
#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;
#[cfg(windows)]
use std::os::windows::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio, Output, ExitStatus};
use std::thread::JoinHandle;
use std::sync::Arc;

// enums defined below
use ExpressionInner::*;
use IoExpressionInner::*;

/// Create a command given a program name and a collection of arguments.
/// See also the `cmd!` macro, which doesn't require a collection.
///
/// # Example
///
/// ```
/// use duct::cmd;
///
/// let args = vec!["foo", "bar", "baz"];
///
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

/// Create a command with any number of of positional arguments, which
/// may be different types (anything that implements `Into<OsString>`).
/// See also the `cmd` function, which takes a collection of arguments.
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
/// However, building shell commands at runtime brings up tricky
/// whitespace and escaping issues, so avoid using `sh` and `format!`
/// together. Prefer `cmd!` instead in those cases. Also note that shell
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

#[derive(Clone, Debug)]
#[must_use]
pub struct Expression {
    inner: Arc<ExpressionInner>,
}

impl Expression {
    pub fn run(&self) -> Result<Output, Error> {
        let (context, stdout_reader, stderr_reader) = IoContext::new()?;
        let status = self.inner.exec(context)?;
        // These unwraps propagate any panics from the other thread,
        // but regular errors return normally.
        let stdout_vec = stdout_reader.join().unwrap()?;
        let stderr_vec = stderr_reader.join().unwrap()?;
        let output = Output {
            status: status,
            stdout: stdout_vec,
            stderr: stderr_vec,
        };
        if !output.status.success() {
            Err(Error::Status(output))
        } else {
            Ok(output)
        }
    }

    pub fn read(&self) -> Result<String, Error> {
        let output = self.stdout_capture().run()?;
        let output_str = std::str::from_utf8(&output.stdout)?;
        Ok(trim_right_newlines(output_str).to_owned())
    }

    pub fn pipe(&self, right: Expression) -> Expression {
        Self::new(Pipe(self.clone(), right.clone()))
    }

    pub fn then(&self, right: Expression) -> Expression {
        Self::new(Then(self.clone(), right.clone()))
    }

    pub fn input<T: Into<Vec<u8>>>(&self, input: T) -> Self {
        Self::new(Io(Input(input.into()), self.clone()))
    }

    pub fn stdin<T: Into<PathBuf>>(&self, path: T) -> Self {
        Self::new(Io(Stdin(path.into()), self.clone()))
    }

    pub fn stdin_file(&self, file: File) -> Self {
        Self::new(Io(StdinFile(file), self.clone()))
    }

    pub fn stdin_null(&self) -> Self {
        Self::new(Io(StdinNull, self.clone()))
    }

    pub fn stdout<T: Into<PathBuf>>(&self, path: T) -> Self {
        Self::new(Io(Stdout(path.into()), self.clone()))
    }

    pub fn stdout_file(&self, file: File) -> Self {
        Self::new(Io(StdoutFile(file), self.clone()))
    }

    pub fn stdout_null(&self) -> Self {
        Self::new(Io(StdoutNull, self.clone()))
    }

    pub fn stdout_capture(&self) -> Self {
        Self::new(Io(StdoutCapture, self.clone()))
    }

    pub fn stdout_to_stderr(&self) -> Self {
        Self::new(Io(StdoutToStderr, self.clone()))
    }

    pub fn stderr<T: Into<PathBuf>>(&self, path: T) -> Self {
        Self::new(Io(Stderr(path.into()), self.clone()))
    }

    pub fn stderr_file(&self, file: File) -> Self {
        Self::new(Io(StderrFile(file.into()), self.clone()))
    }

    pub fn stderr_null(&self) -> Self {
        Self::new(Io(StderrNull, self.clone()))
    }

    pub fn stderr_capture(&self) -> Self {
        Self::new(Io(StderrCapture, self.clone()))
    }

    pub fn stderr_to_stdout(&self) -> Self {
        Self::new(Io(StderrToStdout, self.clone()))
    }

    pub fn dir<T: Into<PathBuf>>(&self, path: T) -> Self {
        Self::new(Io(Dir(path.into()), self.clone()))
    }

    pub fn env<T, U>(&self, name: T, val: U) -> Self
        where T: Into<OsString>,
              U: Into<OsString>
    {
        Self::new(Io(Env(name.into(), val.into()), self.clone()))
    }

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

    pub fn unchecked(&self) -> Self {
        Self::new(Io(Unchecked, self.clone()))
    }

    fn new(inner: ExpressionInner) -> Self {
        Expression { inner: Arc::new(inner) }
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
    fn exec(&self, context: IoContext) -> io::Result<ExitStatus> {
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

fn exec_argv(argv: &[OsString], context: IoContext) -> io::Result<ExitStatus> {
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
    command.status()
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

fn exec_sh(command: &OsString, context: IoContext) -> io::Result<ExitStatus> {
    exec_argv(&shell_command_argv(command.clone()), context)
}

fn exec_pipe(left: &Expression, right: &Expression, context: IoContext) -> io::Result<ExitStatus> {
    let pipe = os_pipe::pipe()?;
    let mut left_context = context.try_clone()?;  // dup'ing stdin/stdout isn't strictly necessary, but no big deal
    left_context.stdout = IoValue::File(pipe.writer);
    let mut right_context = context;
    right_context.stdin = IoValue::File(pipe.reader);

    let (left_result, right_result) = crossbeam::scope(|scope| {
        let left_joiner = scope.spawn(|| left.inner.exec(left_context));
        let right_result = right.inner.exec(right_context);
        let left_result = left_joiner.join();
        (left_result, right_result)
    });

    let right_status = right_result?;
    let left_status = left_result?;
    if !right_status.success() {
        Ok(right_status)
    } else {
        Ok(left_status)
    }
}

fn exec_then(left: &Expression, right: &Expression, context: IoContext) -> io::Result<ExitStatus> {
    let status = left.inner.exec(context.try_clone()?)?;
    if !status.success() {
        Ok(status)
    } else {
        right.inner.exec(context)
    }
}

fn exec_io(io_inner: &IoExpressionInner,
           expr: &Expression,
           context: IoContext)
           -> io::Result<ExitStatus> {
    {
        crossbeam::scope(|scope| {
            let (new_context, maybe_writer_thread) = io_inner.update_context(context, scope)?;
            let exec_result = expr.inner.exec(new_context);
            let writer_result = join_maybe_writer_thread(maybe_writer_thread);
            // Propagate any exec errors first.
            let exec_status = exec_result?;
            // Then propagate any writer thread errors.
            writer_result?;
            // Finally, implement unchecked() status suppression here.
            if let &Unchecked = io_inner {
                Ok(ExitStatus::from_raw(0))
            } else {
                Ok(exec_status)
            }
        })
    }
}

#[derive(Debug)]
enum IoExpressionInner {
    Input(Vec<u8>),
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
    fn update_context<'a>(&'a self,
                          mut context: IoContext,
                          scope: &crossbeam::Scope<'a>)
                          -> io::Result<(IoContext, Option<WriterThread>)> {
        let mut maybe_thread = None;
        match *self {
            Input(ref v) => {
                let (reader, thread) = pipe_with_writer_thread(v, scope)?;
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

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Utf8(std::str::Utf8Error),
    Status(Output),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::Io(err)
    }
}

impl From<std::str::Utf8Error> for Error {
    fn from(err: std::str::Utf8Error) -> Error {
        Error::Utf8(err)
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
            IoValue::File(f) => Ok(os_pipe::stdio_from_file(f)),
        }
    }
}

type ReaderThread = JoinHandle<io::Result<Vec<u8>>>;

fn pipe_with_reader_thread() -> io::Result<(File, ReaderThread)> {
    let os_pipe::Pipe { mut reader, writer } = os_pipe::pipe()?;
    let thread = std::thread::spawn(move || {
        let mut output = Vec::new();
        reader.read_to_end(&mut output)?;
        Ok(output)
    });
    Ok((writer, thread))
}

type WriterThread = crossbeam::ScopedJoinHandle<io::Result<()>>;

fn pipe_with_writer_thread<'a>(input: &'a [u8],
                               scope: &crossbeam::Scope<'a>)
                               -> io::Result<(File, WriterThread)> {
    let os_pipe::Pipe { reader, mut writer } = os_pipe::pipe()?;
    let thread = scope.spawn(move || {
        writer.write_all(&input)?;
        Ok(())
    });
    Ok((reader, thread))
}

fn join_maybe_writer_thread(maybe_writer_thread: Option<WriterThread>) -> io::Result<()> {
    if let Some(thread) = maybe_writer_thread {
        // A broken pipe error happens if the process on the other end exits before
        // we're done writing. We ignore those but return any other errors to the
        // caller.
        suppress_broken_pipe_errors(thread.join())
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

#[cfg(test)]
mod test {
    extern crate tempdir;
    use self::tempdir::TempDir;

    use super::*;
    use std::collections::HashMap;
    use std::env;
    use std::env::consts::EXE_EXTENSION;
    use std::ffi::{OsStr, OsString};
    use std::fs::File;
    use std::io;
    use std::io::prelude::*;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::str;
    use std::sync::{Once, ONCE_INIT};

    fn path_to_exe(name: &str) -> PathBuf {
        // This project defines some associated binaries for testing, and we shell out to them in
        // these tests. `cargo test` doesn't automatically build associated binaries, so this
        // function takes care of building them explicitly.
        static CARGO_BUILD_ONCE: Once = ONCE_INIT;
        CARGO_BUILD_ONCE.call_once(|| {
            let build_status = Command::new("cargo")
                .arg("build")
                .arg("--quiet")
                .status()
                .unwrap();
            assert!(build_status.success(),
                    "Cargo failed to build associated binaries.");
        });

        Path::new("target").join("debug").join(name).with_extension(EXE_EXTENSION)
    }

    fn true_cmd() -> Expression {
        cmd!(path_to_exe("status"), "0")
    }

    fn false_cmd() -> Expression {
        cmd!(path_to_exe("status"), "1")
    }

    #[test]
    fn test_cmd() {
        // Windows compatible.
        let output = cmd!(path_to_exe("echo"), "hi").read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_sh() {
        // Windows compatible.
        let output = sh("echo hi").read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_error() {
        let result = false_cmd().run();
        if let Err(Error::Status(output)) = result {
            // Check that the status is non-zero.
            assert!(!output.status.success());
        } else {
            panic!("Expected a status error.");
        }
    }

    #[test]
    fn test_unchecked() {
        let unchecked_false = false_cmd().unchecked();
        let output = unchecked_false.then(cmd!(path_to_exe("echo"), "waa"))
            .then(unchecked_false)
            .read()
            .unwrap();
        assert_eq!("waa", output);
    }

    #[test]
    fn test_pipe() {
        let output = sh("echo xxx").pipe(cmd!(path_to_exe("x_to_y"))).read().unwrap();
        assert_eq!("yyy", output);

        // Check that errors on either side are propagated.
        let result = true_cmd().pipe(false_cmd()).run();
        match result {
            Err(Error::Status(output)) => {
                assert!(output.status.code().unwrap() == 1);
            }
            _ => panic!("should never get here"),
        }

        let result = false_cmd().pipe(true_cmd()).run();
        match result {
            Err(Error::Status(output)) => {
                assert!(output.status.code().unwrap() == 1);
            }
            _ => panic!("should never get here"),
        }
    }

    #[test]
    fn test_then() {
        let output = true_cmd().then(sh("echo lo")).read().unwrap();
        assert_eq!("lo", output);

        // Check that errors on either side are propagated.
        let result = true_cmd().then(false_cmd()).run();
        match result {
            Err(Error::Status(output)) => {
                assert!(output.status.code().unwrap() == 1);
            }
            _ => panic!("should never get here"),
        }

        let result = false_cmd().then(true_cmd()).run();
        match result {
            Err(Error::Status(output)) => {
                assert!(output.status.code().unwrap() == 1);
            }
            _ => panic!("should never get here"),
        }
    }

    #[test]
    fn test_input() {
        let expr = cmd!(path_to_exe("x_to_y")).input("xxx");
        let output = expr.read().unwrap();
        assert_eq!("yyy", output);
    }

    #[test]
    fn test_stderr() {
        let mut pipe = ::os_pipe::pipe().unwrap();
        sh("echo hi>&2").stderr_file(pipe.writer).run().unwrap();
        let mut s = String::new();
        pipe.reader.read_to_string(&mut s).unwrap();
        assert_eq!(s.trim(), "hi");
    }

    #[test]
    fn test_null() {
        let expr = cmd!(path_to_exe("cat"))
            .stdin_null()
            .stdout_null()
            .stderr_null();
        let output = expr.read().unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_path() {
        let dir = TempDir::new("test_path").unwrap();
        let input_file = dir.path().join("input_file");
        let output_file = dir.path().join("output_file");
        File::create(&input_file).unwrap().write_all(b"xxx").unwrap();
        let expr = cmd!(path_to_exe("x_to_y"))
            .stdin(&input_file)
            .stdout(&output_file);
        let output = expr.read().unwrap();
        assert_eq!("", output);
        let mut file_output = String::new();
        File::open(&output_file).unwrap().read_to_string(&mut file_output).unwrap();
        assert_eq!("yyy", file_output);
    }

    #[test]
    fn test_swapping() {
        let output = sh("echo hi")
            .stdout_to_stderr()
            .stderr_capture()
            .run()
            .unwrap();
        let stderr = str::from_utf8(&output.stderr).unwrap().trim();
        assert_eq!("hi", stderr);

        // Windows compatible. (Requires no space before the ">".)
        let output = sh("echo hi>&2").stderr_to_stdout().read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_file() {
        let dir = TempDir::new("test_file").unwrap();
        let file = dir.path().join("file");
        File::create(&file).unwrap().write_all(b"example").unwrap();
        let expr = cmd!(path_to_exe("cat")).stdin_file(File::open(&file).unwrap());
        let output = expr.read().unwrap();
        assert_eq!(output, "example");
    }

    #[test]
    fn test_ergonomics() {
        let mystr = "owned string".to_owned();
        let mypathbuf = Path::new("a/b/c").to_owned();
        let myvec = vec![1, 2, 3];
        // These are nonsense expressions. We just want to make sure they compile.
        let _ = sh("true").stdin(&*mystr).input(&*myvec).stdout(&*mypathbuf);
        let _ = sh("true").stdin(mystr).input(myvec).stdout(mypathbuf);

        // Unfortunately, this one doesn't work with our Into<Vec<u8>> bound on input().
        // TODO: Is it worth having these impls for &Vec in other cases?
        // let _ = sh("true").stdin(&mystr).input(&myvec).stdout(&mypathbuf);
    }

    #[test]
    fn test_capture_both() {
        // Windows compatible, no space before ">", and we trim newlines at the end to avoid
        // dealing with the different kinds.
        let output = sh("echo hi")
            .then(sh("echo lo>&2"))
            .stdout_capture()
            .stderr_capture()
            .run()
            .unwrap();
        assert_eq!("hi", str::from_utf8(&output.stdout).unwrap().trim());
        assert_eq!("lo", str::from_utf8(&output.stderr).unwrap().trim());
    }

    #[test]
    fn test_dir() {
        let pwd = cmd!(path_to_exe("pwd"));

        // First assert that ordinary commands happen in the parent's dir.
        let pwd_output = pwd.read().unwrap();
        let pwd_path = Path::new(&pwd_output);
        assert_eq!(pwd_path, env::current_dir().unwrap());

        // Now create a temp dir and make sure we can set dir to it. This
        // also tests the interaction of `dir` and relative exe paths.
        let dir = TempDir::new("duct_test").unwrap();
        let pwd_output = pwd.dir(dir.path()).read().unwrap();
        let pwd_path = Path::new(&pwd_output);
        // pwd_path isn't totally canonical on Windows, because it
        // doesn't have a prefix. Thus we have to canonicalize both
        // sides. (This also handles symlinks in TMP_DIR.)
        assert_eq!(pwd_path.canonicalize().unwrap(),
                   dir.path().canonicalize().unwrap());
    }

    #[test]
    fn test_env() {
        let output = cmd!(path_to_exe("print_env"), "foo")
            .env("foo", "bar")
            .read()
            .unwrap();
        assert_eq!("bar", output);
    }

    #[test]
    fn test_full_env() {
        let var_name = "test_env_remove_var";

        // Capture the parent env, and make sure it does *not* contain our variable.
        let mut clean_env: HashMap<OsString, OsString> = env::vars_os().collect();
        clean_env.remove(AsRef::<OsStr>::as_ref(var_name));

        // Run a child process with that map passed to full_env(). It should be guaranteed not to
        // see our variable, regardless of any outer env() calls or changes in the parent.
        let clean_child = cmd!(path_to_exe("print_env"), var_name).full_env(clean_env);

        // Dirty the parent env. Should be suppressed.
        env::set_var(var_name, "junk1");
        // And make an outer env() call. Should also be suppressed.
        let dirty_child = clean_child.env(var_name, "junk2");

        // Check that neither of those have any effect.
        let output = dirty_child.read().unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_broken_pipe() {
        // If the input writing thread fills up its pipe buffer, writing will block. If the process
        // on the other end of the pipe exits while writer is waiting, the write will return an
        // error. We need to swallow that error, rather than returning it.
        let myvec = vec![0; 1_000_000];
        true_cmd().input(myvec).run().unwrap();
    }

    #[test]
    fn test_suppress_broken_pipe() {
        let broken_pipe_error = Err(io::Error::new(io::ErrorKind::BrokenPipe, ""));
        assert!(::suppress_broken_pipe_errors(broken_pipe_error).is_ok());

        let other_error = Err(io::Error::new(io::ErrorKind::Other, ""));
        assert!(::suppress_broken_pipe_errors(other_error).is_err());
    }

    #[test]
    fn test_silly() {
        // A silly test, purely for coverage.
        ::IoValue::Null.try_clone().unwrap();
    }

    #[test]
    fn test_path_sanitization() {
        // We don't do any chdir'ing in this process, because the tests runner is multithreaded,
        // and we don't want to screw up anyone else's relative paths. Instead, we shell out to a
        // small test process that does that for us.
        cmd!(path_to_exe("exe_in_dir"), path_to_exe("status"), "0")
            .run()
            .unwrap();
    }
}
