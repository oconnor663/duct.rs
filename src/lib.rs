extern crate crossbeam;
extern crate os_pipe;

use std::borrow::Borrow;
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

pub fn cmd<T: AsRef<OsStr>>(argv: &[T]) -> Expression {
    let argv_vec = argv.iter().map(|arg| arg.as_ref().to_owned()).collect();
    Expression::new(Cmd(argv_vec))
}

#[macro_export]
macro_rules! cmd {
    ( $( $x:expr ),* ) => {
        {
            use std::ffi::OsStr;
            let mut temp_vec = Vec::new();
            $(
                let temp_arg = $x;
                let temp_osstr: &OsStr = temp_arg.as_ref();
                temp_vec.push(temp_osstr.to_owned());
            )*
            $crate::cmd(&temp_vec)
        }
    };
}

pub fn sh<T: AsRef<OsStr>>(command: T) -> Expression {
    Expression::new(Sh(command.as_ref().to_owned()))
}

#[derive(Clone, Debug)]
#[must_use]
pub struct Expression {
    inner: Arc<ExpressionInner>,
}

impl Expression {
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
        if !output.status.success() {
            Err(Error::Status(output))
        } else {
            Ok(output)
        }
    }

    pub fn read(&self) -> Result<String, Error> {
        let output = try!(self.capture_stdout().run());
        let output_str = try!(std::str::from_utf8(&output.stdout));
        Ok(trim_right_newlines(output_str).to_owned())
    }

    pub fn pipe<T: Borrow<Expression>>(&self, right: T) -> Expression {
        Self::new(Pipe(self.clone(), right.borrow().clone()))
    }

    pub fn then<T: Borrow<Expression>>(&self, right: T) -> Expression {
        Self::new(Then(self.clone(), right.borrow().clone()))
    }

    pub fn input<T: AsRef<[u8]>>(&self, input: T) -> Self {
        Self::new(Io(Input(input.as_ref().to_vec()), self.clone()))
    }

    pub fn stdin<T: Into<FileOpener>>(&self, stdin: T) -> Self {
        Self::new(Io(Stdin(stdin.into()), self.clone()))
    }

    pub fn null_stdin(&self) -> Self {
        Self::new(Io(StdinNull, self.clone()))
    }

    pub fn stdout<T: Into<FileOpener>>(&self, stdout: T) -> Self {
        Self::new(Io(Stdout(stdout.into()), self.clone()))
    }

    pub fn null_stdout(&self) -> Self {
        Self::new(Io(StdoutNull, self.clone()))
    }

    pub fn capture_stdout(&self) -> Self {
        Self::new(Io(StdoutCapture, self.clone()))
    }

    pub fn stdout_to_stderr(&self) -> Self {
        Self::new(Io(StdoutToStderr, self.clone()))
    }

    pub fn stderr<T: Into<FileOpener>>(&self, stderr: T) -> Self {
        Self::new(Io(Stderr(stderr.into()), self.clone()))
    }

    pub fn null_stderr(&self) -> Self {
        Self::new(Io(StderrNull, self.clone()))
    }

    pub fn capture_stderr(&self) -> Self {
        Self::new(Io(StderrCapture, self.clone()))
    }

    pub fn stderr_to_stdout(&self) -> Self {
        Self::new(Io(StderrToStdout, self.clone()))
    }

    pub fn dir<T: AsRef<Path>>(&self, path: T) -> Self {
        Self::new(Io(Dir(path.as_ref().to_owned()), self.clone()))
    }

    pub fn env<T: AsRef<OsStr>, U: AsRef<OsStr>>(&self, name: T, val: U) -> Self {
        Self::new(Io(Env(name.as_ref().to_owned(), val.as_ref().to_owned()),
                     self.clone()))
    }

    pub fn full_env<T, U, V>(&self, name_vals: T) -> Self
        where T: IntoIterator<Item = (U, V)>,
              U: AsRef<OsStr>,
              V: AsRef<OsStr>
    {
        let env_map = name_vals.into_iter()
            .map(|(k, v)| (k.as_ref().to_owned(), v.as_ref().to_owned()))
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

fn exec_argv(argv: &[OsString], context: IoContext) -> io::Result<ExitStatus> {
    let mut command = Command::new(&argv[0]);
    command.args(&argv[1..]);
    // TODO: Avoid unnecessary dup'ing here.
    command.stdin(try!(context.stdin.into_stdio()));
    command.stdout(try!(context.stdout.into_stdio()));
    command.stderr(try!(context.stderr.into_stdio()));
    command.current_dir(context.dir);
    command.env_clear();
    for (name, val) in context.env {
        command.env(name, val);
    }
    Ok(try!(command.status()))
}

fn exec_sh(command: &OsString, context: IoContext) -> io::Result<ExitStatus> {
    // TODO: Use COMSPEC on Windows, as Python does. https://docs.python.org/3/library/subprocess.html
    let mut argv: Vec<OsString> = Vec::new();
    argv.push(AsRef::<OsStr>::as_ref("/bin/sh").to_owned());
    argv.push(AsRef::<OsStr>::as_ref("-c").to_owned());
    argv.push(command.to_owned());
    exec_argv(&argv, context)
}

fn exec_pipe(left: &Expression, right: &Expression, context: IoContext) -> io::Result<ExitStatus> {
    let pair = try!(os_pipe::pipe());
    let mut left_context = try!(context.try_clone());  // dup'ing stdin/stdout isn't strictly necessary, but no big deal
    left_context.stdout = IoValue::File(pair.write);
    let mut right_context = context;
    right_context.stdin = IoValue::File(pair.read);

    let (left_result, right_result) = crossbeam::scope(|scope| {
        let left_joiner = scope.spawn(|| left.inner.exec(left_context));
        let right_result = right.inner.exec(right_context);
        let left_result = left_joiner.join();
        (left_result, right_result)
    });

    let right_status = try!(right_result);
    let left_status = try!(left_result);
    if !right_status.success() {
        Ok(right_status)
    } else {
        Ok(left_status)
    }
}

fn exec_then(left: &Expression, right: &Expression, context: IoContext) -> io::Result<ExitStatus> {
    let status = try!(left.inner.exec(try!(context.try_clone())));
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
            let (new_context, maybe_writer_thread) = try!(io_inner.update_context(context, scope));
            let exec_result = expr.inner.exec(new_context);
            let writer_result = join_maybe_writer_thread(maybe_writer_thread);
            // Propagate any exec errors first.
            let exec_status = try!(exec_result);
            // Then propagate any writer thread errors.
            try!(writer_result);
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
    Stdin(FileOpener),
    StdinNull,
    Stdout(FileOpener),
    StdoutNull,
    StdoutCapture,
    StdoutToStderr,
    Stderr(FileOpener),
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
                let (reader, thread) = try!(pipe_with_writer_thread(v, scope));
                context.stdin = IoValue::File(reader);
                maybe_thread = Some(thread)
            }
            Stdin(ref f) => {
                context.stdin = IoValue::File(try!(f.open_for_reading()));
            }
            StdinNull => {
                context.stdin = IoValue::Null;
            }
            Stdout(ref f) => {
                context.stdout = IoValue::File(try!(f.open_for_writing()));
            }
            StdoutNull => {
                context.stdout = IoValue::Null;
            }
            StdoutCapture => {
                context.stdout = IoValue::File(try!(context.stdout_capture.try_clone()))
            }
            StdoutToStderr => {
                context.stdout = try!(context.stderr.try_clone());
            }
            Stderr(ref f) => {
                context.stderr = IoValue::File(try!(f.open_for_writing()));
            }
            StderrNull => {
                context.stderr = IoValue::Null;
            }
            StderrCapture => {
                context.stderr = IoValue::File(try!(context.stderr_capture.try_clone()))
            }
            StderrToStdout => {
                context.stderr = try!(context.stdout.try_clone());
            }
            Dir(ref p) => {
                context.dir = p.clone();
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

#[derive(Debug)]
pub enum FileOpener {
    PathBuf(PathBuf),
    File(File),
}

impl FileOpener {
    fn open_for_reading(&self) -> io::Result<File> {
        match *self {
            FileOpener::PathBuf(ref p) => File::open(p),
            FileOpener::File(ref f) => f.try_clone(),
        }
    }

    fn open_for_writing(&self) -> io::Result<File> {
        match *self {
            FileOpener::PathBuf(ref p) => File::create(p),
            FileOpener::File(ref f) => f.try_clone(),
        }
    }
}

impl From<File> for FileOpener {
    fn from(f: File) -> FileOpener {
        FileOpener::File(f)
    }
}

// TODO: Get rid of most of these impl's once specialization lands.

impl<'a> From<&'a str> for FileOpener {
    fn from(s: &str) -> FileOpener {
        FileOpener::PathBuf(AsRef::<Path>::as_ref(s).to_owned())
    }
}

impl<'a> From<&'a String> for FileOpener {
    fn from(s: &String) -> FileOpener {
        FileOpener::PathBuf(s.clone().into())
    }
}

impl From<String> for FileOpener {
    fn from(s: String) -> FileOpener {
        FileOpener::PathBuf(s.into())
    }
}

impl<'a> From<&'a Path> for FileOpener {
    fn from(p: &Path) -> FileOpener {
        FileOpener::PathBuf(p.to_owned())
    }
}

impl<'a> From<&'a PathBuf> for FileOpener {
    fn from(p: &PathBuf) -> FileOpener {
        FileOpener::PathBuf(p.clone())
    }
}

impl From<PathBuf> for FileOpener {
    fn from(p: PathBuf) -> FileOpener {
        FileOpener::PathBuf(p)
    }
}

impl<'a> From<&'a OsStr> for FileOpener {
    fn from(s: &OsStr) -> FileOpener {
        FileOpener::PathBuf(s.clone().into())
    }
}

impl<'a> From<&'a OsString> for FileOpener {
    fn from(s: &OsString) -> FileOpener {
        FileOpener::PathBuf(AsRef::<Path>::as_ref(s).to_owned())
    }
}

impl From<OsString> for FileOpener {
    fn from(s: OsString) -> FileOpener {
        FileOpener::PathBuf(s.into())
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
pub struct IoContext {
    stdin: IoValue,
    stdout: IoValue,
    stderr: IoValue,
    stdout_capture: File,
    stderr_capture: File,
    dir: PathBuf,
    env: HashMap<OsString, OsString>,
}

impl IoContext {
    // Returns (context, stdout_reader, stderr_reader).
    fn new() -> io::Result<(IoContext, ReaderThread, ReaderThread)> {
        let (stdout_capture, stdout_reader) = try!(pipe_with_reader_thread());
        let (stderr_capture, stderr_reader) = try!(pipe_with_reader_thread());
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
            dir: try!(std::env::current_dir()),
            env: env,
        };
        Ok((context, stdout_reader, stderr_reader))
    }

    fn try_clone(&self) -> io::Result<IoContext> {
        Ok(IoContext {
            stdin: try!(self.stdin.try_clone()),
            stdout: try!(self.stdout.try_clone()),
            stderr: try!(self.stderr.try_clone()),
            stdout_capture: try!(self.stdout_capture.try_clone()),
            stderr_capture: try!(self.stderr_capture.try_clone()),
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
            &IoValue::File(ref f) => IoValue::File(try!(f.try_clone())),
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
    let os_pipe::Pair { mut read, write } = try!(os_pipe::pipe());
    let thread = std::thread::spawn(move || {
        let mut output = Vec::new();
        try!(read.read_to_end(&mut output));
        Ok(output)
    });
    Ok((write, thread))
}

type WriterThread = crossbeam::ScopedJoinHandle<io::Result<()>>;

fn pipe_with_writer_thread<'a>(input: &'a [u8],
                               scope: &crossbeam::Scope<'a>)
                               -> io::Result<(File, WriterThread)> {
    let os_pipe::Pair { read, mut write } = try!(os_pipe::pipe());
    let thread = scope.spawn(move || {
        try!(write.write_all(&input));
        Ok(())
    });
    Ok((read, thread))
}

fn join_maybe_writer_thread(maybe_writer_thread: Option<WriterThread>) -> io::Result<()> {
    if let Some(thread) = maybe_writer_thread {
        if let Err(thread_error) = thread.join() {
            // A broken pipe error happens if the process on the other end exits before
            // we're done writing. We ignore those but return any other errors to the
            // caller.
            if thread_error.kind() != io::ErrorKind::BrokenPipe {
                return Err(thread_error);
            }
        }
    }
    Ok(())
}

fn trim_right_newlines(s: &str) -> &str {
    s.trim_right_matches(|c| c == '\n' || c == '\r')
}

#[cfg(test)]
mod test {
    extern crate tempdir;
    use self::tempdir::TempDir;

    use super::*;
    use std::env;
    use std::fs::File;
    use std::io::prelude::*;
    use std::path::{Path, PathBuf};
    use std::collections::HashMap;

    fn path_to_test_binary(name: &str) -> PathBuf {
        let test_project = Path::new(".").join("test").join(name);
        // Build the test command.
        sh("cargo build --quiet")
            .dir(&test_project)
            .run()
            .expect(&format!("building test command '{}' returned an error", name));
        // Return the path to the built binary.
        test_project.join("target").join("debug").join(name)
    }

    #[test]
    fn test_cmd() {
        // Windows compatible.
        let output = cmd!("echo", "hi").read().unwrap();
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
        let result = cmd!(path_to_test_binary("status"), "1").run();
        if let Err(Error::Status(output)) = result {
            // Check that the status is non-zero.
            assert!(!output.status.success());
        } else {
            panic!("Expected a status error.");
        }
    }

    #[test]
    fn test_ignore() {
        let ignored_false = cmd!(path_to_test_binary("status"), "1").unchecked();
        let output = ignored_false.then(cmd!("echo", "waa")).then(ignored_false).read().unwrap();
        assert_eq!("waa", output);
    }

    #[test]
    fn test_pipe() {
        let output = sh("echo xxx").pipe(cmd!(path_to_test_binary("x_to_y"))).read().unwrap();
        assert_eq!("yyy", output);
    }

    #[test]
    fn test_then() {
        let output = cmd!(path_to_test_binary("status"), "0").then(sh("echo lo")).read().unwrap();
        assert_eq!("lo", output);
    }

    #[test]
    fn test_input() {
        // TODO: Fixed-length bytes input like b"foo" works poorly here. Why?
        let expr = cmd!(path_to_test_binary("x_to_y")).input("xxx");
        let output = expr.read().unwrap();
        assert_eq!("yyy", output);
    }

    #[test]
    fn test_null() {
        let expr = cmd!("cat").null_stdin().null_stdout().null_stderr();
        let output = expr.read().unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_path() {
        let dir = TempDir::new("test_path").unwrap();
        let input_file = dir.path().join("input_file");
        let output_file = dir.path().join("output_file");
        File::create(&input_file).unwrap().write_all(b"xxx").unwrap();
        let expr = cmd!(path_to_test_binary("x_to_y"))
            .stdin(&input_file)
            .stdout(&output_file);
        let output = expr.read().unwrap();
        assert_eq!("", output);
        let mut file_output = String::new();
        File::open(&output_file).unwrap().read_to_string(&mut file_output).unwrap();
        assert_eq!("yyy", file_output);
    }

    #[test]
    fn test_stderr_to_stdout() {
        // Windows compatible. (Requires no space before the ">".)
        let command = sh("echo hi>&2").stderr_to_stdout();
        let output = command.read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_file() {
        let dir = TempDir::new("test_file").unwrap();
        let file = dir.path().join("file");
        File::create(&file).unwrap().write_all(b"example").unwrap();
        let expr = cmd!("cat").stdin(File::open(&file).unwrap());
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
        let _ = sh("true").stdin(&mystr).input(&myvec).stdout(&mypathbuf);
        let _ = sh("true").stdin(mystr).input(myvec).stdout(mypathbuf);
    }

    #[test]
    fn test_capture_both() {
        let output = sh("echo -n hi; echo -n lo >&2")
            .capture_stdout()
            .capture_stderr()
            .run()
            .unwrap();
        assert_eq!(b"hi", &*output.stdout);
        assert_eq!(b"lo", &*output.stderr);
    }

    #[test]
    fn test_cwd() {
        // First assert that ordinary commands happen in the parent's dir.
        let pwd_output = cmd!("pwd").read().unwrap();
        let pwd_path = Path::new(&pwd_output);
        assert_eq!(pwd_path, env::current_dir().unwrap());

        // Now create a temp dir and make sure we can set dir to it.
        let dir = TempDir::new("duct_test").unwrap();
        let pwd_output = cmd!("pwd").dir(dir.path()).read().unwrap();
        let pwd_path = Path::new(&pwd_output);
        assert_eq!(pwd_path, dir.path());
    }

    #[test]
    fn test_env() {
        let output = sh("echo $foo").env("foo", "bar").read().unwrap();
        assert_eq!("bar", output);
    }

    #[test]
    fn test_full_env() {
        // Set a var twice, both in the parent process and with an env() call. Make sure a single
        // full_env() call clears both.
        let var_name = "test_env_remove_var";
        env::set_var(var_name, "junk1");
        let command = format!("echo ${}", var_name);
        let output = sh(command)
            .full_env(HashMap::<String, String>::new())
            .env(var_name, "junk2")
            .read()
            .unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_broken_pipe() {
        // If the input writing thread fills up its pipe buffer, writing will block. If the process
        // on the other end of the pipe exits while writer is waiting, the write will return an
        // error. We need to swallow that error, rather than returning it.
        let myvec = vec![0; 1_000_000];
        cmd!("true").input(myvec).run().unwrap();
    }
}
