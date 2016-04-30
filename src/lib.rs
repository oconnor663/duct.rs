extern crate crossbeam;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::thread::JoinHandle;
use std::sync::Arc;

// enums defined below
use ExpressionInner::*;
use ExecutableExpression::*;
use IoArg::*;

mod pipe;

pub fn cmd<T: AsRef<OsStr>>(argv: &[T]) -> Expression<'static> {
    let argv_vec = argv.iter().map(|arg| arg.as_ref().to_owned()).collect();
    Expression::new(Exec(ArgvCommand(argv_vec)))
}

#[macro_export]
macro_rules! cmd {
    ( $( $x:expr ),* ) => {
        {
            use std::ffi::OsStr;
            let mut temp_vec = Vec::new();
            $(
                let temp_osstr: &OsStr = $x.as_ref();
                temp_vec.push(temp_osstr.to_owned());
            )*
            $crate::cmd(&temp_vec)
        }
    };
}

pub fn sh<T: AsRef<OsStr>>(command: T) -> Expression<'static> {
    Expression {
        inner: Arc::new(Exec(ShCommand(command.as_ref()
                                              .to_owned()))),
    }
}

#[derive(Clone, Debug)]
pub struct Expression<'a> {
    inner: Arc<ExpressionInner<'a>>,
}

impl<'a, 'b> Expression<'a>
    where 'b: 'a
{
    pub fn run(&self) -> Result<Output, Error> {
        let (context, stdout_reader, stderr_reader) = try!(IoContext::new());
        let status = try!(self.inner.exec(context));
        let stdout_vec = try!(stdout_reader.join().unwrap());
        let stderr_vec = try!(stderr_reader.join().unwrap());
        let output = Output {
            status: status,
            stdout: stdout_vec,
            stderr: stderr_vec,
        };
        if output.status != 0 {
            Err(Error::Status(output))
        } else {
            Ok(output)
        }
    }

    pub fn read(&self) -> Result<String, Error> {
        let output = try!(self.stdout(OutputRedirect::Capture).run());
        let output_str = try!(std::str::from_utf8(&output.stdout));
        // TODO: Handle Windows newlines too.
        Ok(output_str.trim_right_matches('\n').to_owned())
    }

    pub fn pipe<T: Borrow<Expression<'b>>>(&self, right: T) -> Expression<'a> {
        Self::new(Exec(Pipe(self.clone(), right.borrow().clone())))
    }

    pub fn then<T: Borrow<Expression<'b>>>(&self, right: T) -> Expression<'a> {
        Self::new(Exec(Then(self.clone(), right.borrow().clone())))
    }

    pub fn input<T: IntoStdinBytes<'b>>(&self, input: T) -> Self {
        Self::new(Io(Stdin(input.into_stdin_bytes()), self.clone()))
    }

    pub fn stdin<T: IntoStdin<'b>>(&self, stdin: T) -> Self {
        Self::new(Io(Stdin(stdin.into_stdin()), self.clone()))
    }

    pub fn stdout<T: IntoOutput<'b>>(&self, stdout: T) -> Self {
        Self::new(Io(Stdout(stdout.into_output()), self.clone()))
    }

    pub fn stderr<T: IntoOutput<'b>>(&self, stderr: T) -> Self {
        Self::new(Io(Stderr(stderr.into_output()), self.clone()))
    }

    pub fn cwd<T: AsRef<Path>>(&self, path: T) -> Self {
        Self::new(Io(Cwd(path.as_ref().to_owned()), self.clone()))
    }

    pub fn env<T: AsRef<OsStr>, U: AsRef<OsStr>>(&self, name: T, val: U) -> Self {
        Self::new(Io(Env(name.as_ref().to_owned(), val.as_ref().to_owned()),
                     self.clone()))
    }

    pub fn env_remove<T: AsRef<OsStr>>(&self, name: T) -> Self {
        Self::new(Io(EnvRemove(name.as_ref().to_owned()), self.clone()))
    }

    pub fn env_clear(&self) -> Self {
        Self::new(Io(EnvClear, self.clone()))
    }

    pub fn ignore(&self) -> Self {
        Self::new(Io(IgnoreStatus, self.clone()))
    }

    fn new(inner: ExpressionInner<'a>) -> Self {
        Expression { inner: Arc::new(inner) }
    }
}

#[derive(Debug)]
enum ExpressionInner<'a> {
    Exec(ExecutableExpression<'a>),
    Io(IoArg<'a>, Expression<'a>),
}

impl<'a> ExpressionInner<'a> {
    fn exec(&self, parent_context: IoContext) -> io::Result<Status> {
        match *self {
            Exec(ref executable) => executable.exec(parent_context),
            Io(ref ioarg, ref expr) => {
                ioarg.with_child_context(parent_context, |context| expr.inner.exec(context))
            }
        }
    }
}

#[derive(Debug)]
enum ExecutableExpression<'a> {
    ArgvCommand(Vec<OsString>),
    ShCommand(OsString),
    Pipe(Expression<'a>, Expression<'a>),
    Then(Expression<'a>, Expression<'a>),
}

impl<'a> ExecutableExpression<'a> {
    fn exec(&self, context: IoContext) -> io::Result<Status> {
        match *self {
            ArgvCommand(ref argv) => exec_argv(argv, context),
            ShCommand(ref command) => exec_sh(command, context),
            Pipe(ref left, ref right) => exec_pipe(left, right, context),
            Then(ref left, ref right) => exec_then(left, right, context),
        }
    }
}

fn exec_argv<T: AsRef<OsStr>>(argv: &[T], context: IoContext) -> io::Result<Status> {
    let mut command = Command::new(&argv[0]);
    command.args(&argv[1..]);
    command.stdin(context.stdin.into_stdio());
    command.stdout(context.stdout.into_stdio());
    command.stderr(context.stderr.into_stdio());
    command.current_dir(context.cwd);
    command.env_clear();
    for (name, val) in context.env {
        command.env(name, val);
    }
    Ok(try!(command.status()).code().unwrap()) // TODO: Handle signals.
}

fn exec_sh<T: AsRef<OsStr>>(command: T, context: IoContext) -> io::Result<Status> {
    // TODO: Use COMSPEC on Windows, as Python does. https://docs.python.org/3/library/subprocess.html
    let mut argv = Vec::new();
    argv.push("/bin/sh".as_ref());
    argv.push("-c".as_ref());
    argv.push(command.as_ref());
    exec_argv(&argv, context)
}

fn exec_pipe(left: &Expression, right: &Expression, context: IoContext) -> io::Result<Status> {
    let (read_pipe, write_pipe) = pipe::open_pipe();
    let mut left_context = context.clone();  // dup'ing stdin/stdout isn't strictly necessary, but no big deal
    left_context.stdout = write_pipe;
    let mut right_context = context;
    right_context.stdin = read_pipe;

    let (left_result, right_result) = crossbeam::scope(|scope| {
        let left_joiner = scope.spawn(|| left.inner.exec(left_context));
        let right_result = right.inner.exec(right_context);
        let left_result = left_joiner.join();
        (left_result, right_result)
    });

    let right_status = try!(right_result);
    let left_status = try!(left_result);
    if right_status != 0 {
        Ok(right_status)
    } else {
        Ok(left_status)
    }
}

fn exec_then(left: &Expression, right: &Expression, context: IoContext) -> io::Result<Status> {
    let status = try!(left.inner.exec(context.clone()));
    if status != 0 {
        Ok(status)
    } else {
        right.inner.exec(context)
    }
}

#[derive(Debug)]
enum IoArg<'a> {
    Stdin(InputRedirect<'a>),
    Stdout(OutputRedirect<'a>),
    Stderr(OutputRedirect<'a>),
    Cwd(PathBuf),
    Env(OsString, OsString),
    EnvRemove(OsString),
    EnvClear,
    IgnoreStatus,
}

impl<'a> IoArg<'a> {
    fn with_child_context<F>(&self, parent_context: IoContext, inner: F) -> io::Result<Status>
        where F: FnOnce(IoContext) -> io::Result<Status>
    {
        crossbeam::scope(|scope| {
            let mut context = parent_context;  // move it into the closure
            let mut maybe_stdin_thread = None;
            let mut ignore = false;

            // Put together the redirected context.
            match *self {
                Stdin(ref redir) => {
                    let (handle, maybe_thread) = try!(redir.open_handle_maybe_thread(scope));
                    maybe_stdin_thread = maybe_thread;
                    context.stdin = handle;
                }
                Stdout(ref redir) => {
                    context.stdout = try!(redir.open_handle(&context.stdout,
                                                            &context.stderr,
                                                            &context.stdout_capture));
                }
                Stderr(ref redir) => {
                    context.stderr = try!(redir.open_handle(&context.stdout,
                                                            &context.stderr,
                                                            &context.stderr_capture));
                }
                Cwd(ref path) => {
                    context.cwd = path.to_owned();
                }
                Env(ref name, ref val) => {
                    context.env.insert(name.to_owned(), val.to_owned());
                }
                EnvRemove(ref name) => {
                    context.env.remove(name);
                }
                EnvClear => {
                    context.env.clear();
                }
                IgnoreStatus => {
                    ignore = true;
                }
            }

            // Run the inner closure.
            let status = try!(inner(context));

            // Join the input thread, if any.
            if let Some(thread) = maybe_stdin_thread {
                try!(thread.join());
            }

            if ignore {
                // Return status 0 (success) for ignored expressions.
                Ok(0)
            } else {
                // Otherwise return the real status.
                Ok(status)
            }
        })
    }
}

#[derive(Debug)]
pub enum InputRedirect<'a> {
    Null,
    Path(&'a Path),
    PathBuf(PathBuf),
    FileRef(&'a File),
    File(File),
    BytesSlice(&'a [u8]),
    BytesVec(Vec<u8>),
}

impl<'a> InputRedirect<'a> {
    fn open_handle_maybe_thread(&'a self,
                                scope: &crossbeam::Scope<'a>)
                                -> io::Result<(pipe::Handle, Option<WriterThread>)> {
        let mut maybe_thread = None;
        let handle = match *self {
            InputRedirect::Null => pipe::Handle::from_file(try!(File::open("/dev/null"))),  // TODO: Windows
            InputRedirect::Path(ref p) => pipe::Handle::from_file(try!(File::open(p))),
            InputRedirect::PathBuf(ref p) => pipe::Handle::from_file(try!(File::open(p))),
            InputRedirect::FileRef(ref f) => pipe::Handle::dup_file(f),
            InputRedirect::File(ref f) => pipe::Handle::dup_file(f),
            InputRedirect::BytesSlice(ref b) => {
                let (handle, thread) = pipe_with_writer_thread(b, scope);
                maybe_thread = Some(thread);
                handle
            }
            InputRedirect::BytesVec(ref b) => {
                let (handle, thread) = pipe_with_writer_thread(b, scope);
                maybe_thread = Some(thread);
                handle
            }
        };
        Ok((handle, maybe_thread))
    }
}

pub trait IntoStdinBytes<'a> {
    fn into_stdin_bytes(self) -> InputRedirect<'a>;
}

impl<'a> IntoStdinBytes<'a> for &'a [u8] {
    fn into_stdin_bytes(self) -> InputRedirect<'a> {
        InputRedirect::BytesSlice(self)
    }
}

impl<'a> IntoStdinBytes<'a> for &'a Vec<u8> {
    fn into_stdin_bytes(self) -> InputRedirect<'a> {
        InputRedirect::BytesSlice(self.as_ref())
    }
}

impl IntoStdinBytes<'static> for Vec<u8> {
    fn into_stdin_bytes(self) -> InputRedirect<'static> {
        InputRedirect::BytesVec(self)
    }
}

impl<'a> IntoStdinBytes<'a> for &'a str {
    fn into_stdin_bytes(self) -> InputRedirect<'a> {
        InputRedirect::BytesSlice(self.as_ref())
    }
}

impl<'a> IntoStdinBytes<'a> for &'a String {
    fn into_stdin_bytes(self) -> InputRedirect<'a> {
        InputRedirect::BytesSlice(self.as_ref())
    }
}

impl IntoStdinBytes<'static> for String {
    fn into_stdin_bytes(self) -> InputRedirect<'static> {
        InputRedirect::BytesVec(self.into_bytes())
    }
}

pub trait IntoStdin<'a> {
    fn into_stdin(self) -> InputRedirect<'a>;
}

impl<'a> IntoStdin<'a> for InputRedirect<'a> {
    fn into_stdin(self) -> InputRedirect<'a> {
        self
    }
}

impl<'a> IntoStdin<'a> for &'a Path {
    fn into_stdin(self) -> InputRedirect<'a> {
        InputRedirect::Path(self)
    }
}

impl<'a> IntoStdin<'a> for &'a PathBuf {
    fn into_stdin(self) -> InputRedirect<'a> {
        InputRedirect::Path(self.as_ref())
    }
}

impl IntoStdin<'static> for PathBuf {
    fn into_stdin(self) -> InputRedirect<'static> {
        InputRedirect::PathBuf(self)
    }
}

impl<'a> IntoStdin<'a> for &'a str {
    fn into_stdin(self) -> InputRedirect<'a> {
        InputRedirect::Path(self.as_ref())
    }
}

impl<'a> IntoStdin<'a> for &'a String {
    fn into_stdin(self) -> InputRedirect<'a> {
        InputRedirect::Path(self.as_ref())
    }
}

impl IntoStdin<'static> for String {
    fn into_stdin(self) -> InputRedirect<'static> {
        InputRedirect::PathBuf(self.into())
    }
}

impl<'a> IntoStdin<'a> for &'a OsStr {
    fn into_stdin(self) -> InputRedirect<'a> {
        InputRedirect::Path(self.as_ref())
    }
}

impl<'a> IntoStdin<'a> for &'a OsString {
    fn into_stdin(self) -> InputRedirect<'a> {
        InputRedirect::Path(self.as_ref())
    }
}

impl IntoStdin<'static> for OsString {
    fn into_stdin(self) -> InputRedirect<'static> {
        InputRedirect::PathBuf(self.into())
    }
}

impl<'a> IntoStdin<'a> for &'a File {
    fn into_stdin(self) -> InputRedirect<'a> {
        InputRedirect::FileRef(self)
    }
}

impl IntoStdin<'static> for File {
    fn into_stdin(self) -> InputRedirect<'static> {
        InputRedirect::File(self)
    }
}

#[derive(Debug)]
pub enum OutputRedirect<'a> {
    Capture,
    Null,
    Stdout,
    Stderr,
    Path(&'a Path),
    PathBuf(PathBuf),
    FileRef(&'a File),
    File(File),
}

impl<'a> OutputRedirect<'a> {
    fn open_handle(&self,
                   inherited_stdout: &pipe::Handle,
                   inherited_stderr: &pipe::Handle,
                   capture_handle: &pipe::Handle)
                   -> io::Result<pipe::Handle> {
        Ok(match *self {
            OutputRedirect::Capture => capture_handle.clone(),
            OutputRedirect::Null => pipe::Handle::from_file(try!(File::create("/dev/null"))),  // TODO: Windows
            OutputRedirect::Stdout => inherited_stdout.clone(),
            OutputRedirect::Stderr => inherited_stderr.clone(),
            OutputRedirect::Path(ref p) => pipe::Handle::from_file(try!(File::create(p))),
            OutputRedirect::PathBuf(ref p) => pipe::Handle::from_file(try!(File::create(p))),
            OutputRedirect::FileRef(ref f) => pipe::Handle::dup_file(f),
            OutputRedirect::File(ref f) => pipe::Handle::dup_file(f),
        })
    }
}

pub trait IntoOutput<'a> {
    fn into_output(self) -> OutputRedirect<'a>;
}

impl<'a> IntoOutput<'a> for OutputRedirect<'a> {
    fn into_output(self) -> OutputRedirect<'a> {
        self
    }
}

impl<'a> IntoOutput<'a> for &'a Path {
    fn into_output(self) -> OutputRedirect<'a> {
        OutputRedirect::Path(self)
    }
}

impl<'a> IntoOutput<'a> for &'a PathBuf {
    fn into_output(self) -> OutputRedirect<'a> {
        OutputRedirect::Path(self.as_ref())
    }
}

impl IntoOutput<'static> for PathBuf {
    fn into_output(self) -> OutputRedirect<'static> {
        OutputRedirect::PathBuf(self)
    }
}

impl<'a> IntoOutput<'a> for &'a str {
    fn into_output(self) -> OutputRedirect<'a> {
        OutputRedirect::Path(self.as_ref())
    }
}

impl<'a> IntoOutput<'a> for &'a String {
    fn into_output(self) -> OutputRedirect<'a> {
        OutputRedirect::Path(self.as_ref())
    }
}

impl IntoOutput<'static> for String {
    fn into_output(self) -> OutputRedirect<'static> {
        OutputRedirect::PathBuf(self.into())
    }
}

impl<'a> IntoOutput<'a> for &'a OsStr {
    fn into_output(self) -> OutputRedirect<'a> {
        OutputRedirect::Path(self.as_ref())
    }
}

impl<'a> IntoOutput<'a> for &'a OsString {
    fn into_output(self) -> OutputRedirect<'a> {
        OutputRedirect::Path(self.as_ref())
    }
}

impl IntoOutput<'static> for OsString {
    fn into_output(self) -> OutputRedirect<'static> {
        OutputRedirect::PathBuf(self.into())
    }
}

impl<'a> IntoOutput<'a> for &'a File {
    fn into_output(self) -> OutputRedirect<'a> {
        OutputRedirect::FileRef(self)
    }
}

impl IntoOutput<'static> for File {
    fn into_output(self) -> OutputRedirect<'static> {
        OutputRedirect::File(self)
    }
}

// We can't use std::process::{Output, Status}, because we need to be able to instantiate the
// success status value ourselves.
pub type Status = i32;

#[derive(Clone, Debug)]
pub struct Output {
    pub status: Status,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
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
#[derive(Clone, Debug)]
pub struct IoContext {
    stdin: pipe::Handle,
    stdout: pipe::Handle,
    stderr: pipe::Handle,
    stdout_capture: pipe::Handle,
    stderr_capture: pipe::Handle,
    cwd: PathBuf,
    env: HashMap<OsString, OsString>,
}

impl IoContext {
    // Returns (context, stdout_reader, stderr_reader).
    fn new() -> io::Result<(IoContext, ReaderThread, ReaderThread)> {
        let (stdout_capture, stdout_reader) = pipe_with_reader_thread();
        let (stderr_capture, stderr_reader) = pipe_with_reader_thread();
        let mut env = HashMap::new();
        for (name, val) in std::env::vars_os() {
            env.insert(name, val);
        }
        let context = IoContext {
            stdin: pipe::Handle::stdin(),
            stdout: pipe::Handle::stdout(),
            stderr: pipe::Handle::stderr(),
            stdout_capture: stdout_capture,
            stderr_capture: stderr_capture,
            cwd: try!(std::env::current_dir()),
            env: env,
        };
        Ok((context, stdout_reader, stderr_reader))
    }
}

type ReaderThread = JoinHandle<io::Result<Vec<u8>>>;

fn pipe_with_reader_thread() -> (pipe::Handle, ReaderThread) {
    let (read_pipe, write_pipe) = pipe::open_pipe();
    let thread = std::thread::spawn(move || {
        let mut read_file = read_pipe.into_file();
        let mut output = Vec::new();
        try!(read_file.read_to_end(&mut output));
        Ok(output)
    });
    (write_pipe, thread)
}

type WriterThread = crossbeam::ScopedJoinHandle<io::Result<()>>;

fn pipe_with_writer_thread<'a>(input: &'a [u8],
                               scope: &crossbeam::Scope<'a>)
                               -> (pipe::Handle, WriterThread) {
    let (read_pipe, write_pipe) = pipe::open_pipe();
    let thread = scope.spawn(move || {
        let mut write_file = write_pipe.into_file();
        try!(write_file.write_all(&input));
        Ok(())
    });
    (read_pipe, thread)
}

#[cfg(test)]
mod test {
    extern crate tempfile;
    extern crate tempdir;

    use super::*;
    use std::env;
    use std::io::prelude::*;
    use std::io::SeekFrom;
    use std::path::Path;

    #[test]
    fn test_cmd() {
        let output = cmd!("echo", "hi").read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_sh() {
        let output = sh("echo hi").read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_error() {
        let result = cmd!("false").run();
        if let Err(Error::Status(output)) = result {
            // Check that the status is non-zero.
            assert!(output.status != 0);
        } else {
            panic!("Expected a status error.");
        }
    }

    #[test]
    fn test_ignore() {
        let ignored_false = cmd!("false").ignore();
        let output = ignored_false.then(cmd!("echo", "waa")).then(ignored_false).read().unwrap();
        assert_eq!("waa", output);
    }

    #[test]
    fn test_pipe() {
        let output = sh("echo hi").pipe(sh("sed s/i/o/")).read().unwrap();
        assert_eq!("ho", output);
    }

    #[test]
    fn test_then() {
        let output = sh("echo -n hi").then(sh("echo lo")).read().unwrap();
        assert_eq!("hilo", output);
    }

    #[test]
    fn test_input() {
        // TODO: Fixed-length bytes input like b"foo" works poorly here. Why?
        let expr = sh("sed s/f/g/").input("foo");
        let output = expr.read().unwrap();
        assert_eq!("goo", output);
    }

    #[test]
    fn test_null() {
        // TODO: The separation between InputRedirect and OutputRedirect here is tedious.
        let expr = cmd!("cat")
                       .stdin(InputRedirect::Null)
                       .stdout(OutputRedirect::Null)
                       .stderr(OutputRedirect::Null);
        let output = expr.read().unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_path() {
        let mut input_file = tempfile::NamedTempFile::new().unwrap();
        let output_file = tempfile::NamedTempFile::new().unwrap();
        input_file.write_all(b"foo").unwrap();
        let expr = sh("sed s/o/a/g").stdin(input_file.path()).stdout(output_file.path());
        let output = expr.read().unwrap();
        assert_eq!("", output);
        let mut file_output = String::new();
        output_file.as_ref().read_to_string(&mut file_output).unwrap();
        assert_eq!("faa", file_output);
    }

    #[test]
    fn test_owned_input() {
        fn with_input<'a>(expr: &Expression<'a>) -> Expression<'a> {
            let mystr = format!("I own this: {}", "foo");
            // This would be a lifetime error if we tried to use &mystr.
            expr.input(mystr)
        }

        let c = cmd!("cat");
        let c_with_input = with_input(&c);
        let output = c_with_input.read().unwrap();
        assert_eq!("I own this: foo", output);
    }

    #[test]
    fn test_stderr_to_stdout() {
        let command = sh("echo hi >&2").stderr(OutputRedirect::Stdout);
        let output = command.read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_file() {
        let mut temp = tempfile::NamedTempFile::new().unwrap();
        temp.write_all(b"example").unwrap();
        temp.seek(SeekFrom::Start(0)).unwrap();
        let expr = cmd!("cat").stdin(temp.as_ref());
        let output = expr.read().unwrap();
        assert_eq!(output, "example");
    }

    #[test]
    fn test_ergonomics() {
        // We don't get automatic Deref when we're matching trait implementations, so in addition
        // to implementing String and &str, we *also* implement &String.
        // TODO: See if specialization can clean this up.
        let mystr = "owned string".to_owned();
        let mypathbuf = Path::new("a/b/c").to_owned();
        let myvec = vec![1, 2, 3];
        // These are nonsense expressions. We just want to make sure they compile.
        sh("true").stdin(&*mystr).input(&*myvec).stdout(&*mypathbuf);
        sh("true").stdin(&mystr).input(&myvec).stdout(&mypathbuf);
        sh("true").stdin(mystr).input(myvec).stdout(mypathbuf);
    }

    #[test]
    fn test_capture_both() {
        let output = sh("echo -n hi; echo -n lo >&2")
                         .stdout(OutputRedirect::Capture)
                         .stderr(OutputRedirect::Capture)
                         .run()
                         .unwrap();
        assert_eq!(b"hi", &*output.stdout);
        assert_eq!(b"lo", &*output.stderr);
    }

    #[test]
    fn test_cwd() {
        // First assert that ordinary commands happen in the parent's cwd.
        let pwd_output = cmd!("pwd").read().unwrap();
        let pwd_path = Path::new(&pwd_output);
        assert_eq!(pwd_path, env::current_dir().unwrap());

        // Now create a temp dir and make sure we can set cwd to it.
        let dir = tempdir::TempDir::new("duct_test").unwrap();
        let pwd_output = cmd!("pwd").cwd(dir.path()).read().unwrap();
        let pwd_path = Path::new(&pwd_output);
        assert_eq!(pwd_path, dir.path());
    }

    #[test]
    fn test_env() {
        let output = sh("echo $foo").env("foo", "bar").read().unwrap();
        assert_eq!("bar", output);
    }

    #[test]
    fn test_env_remove() {
        // Set a var twice, both in the parent process and with an env() call. Make sure a single
        // env_remove() call clears both.
        let var_name = "test_env_remove_var";
        env::set_var(var_name, "junk1");
        let command = format!("echo ${}", var_name);
        let output = sh(command).env_remove(var_name).env(var_name, "junk2").read().unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_env_clear() {
        // As test_env_remove, but with env_clear().
        let var_name = "test_env_remove_var";
        env::set_var(var_name, "junk1");
        let command = format!("echo ${}", var_name);
        let output = sh(command).env_clear().env(var_name, "junk2").read().unwrap();
        assert_eq!("", output);
    }
}
