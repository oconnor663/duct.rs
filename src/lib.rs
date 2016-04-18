extern crate crossbeam;

use std::borrow::Borrow;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::path::Path;
use std::process::{Command, Output, ExitStatus};
use std::thread::JoinHandle;
use std::sync::Arc;

mod pipe;

pub fn cmd<T: AsRef<OsStr>>(argv: &[T]) -> Expression<'static> {
    let argv_vec = argv.iter().map(|arg| arg.as_ref().to_owned()).collect();
    Expression {
        inner: Arc::new(ExpressionInner::Exec(ExecutableExpression::ArgvCommand(argv_vec))),
    }
}

pub fn sh<T: AsRef<OsStr>>(command: T) -> Expression<'static> {
    Expression {
        inner: Arc::new(ExpressionInner::Exec(ExecutableExpression::ShCommand(command.as_ref()
                                                                                     .to_owned()))),
    }
}

#[derive(Clone, Debug)]
pub struct Expression<'a> {
    inner: Arc<ExpressionInner<'a>>,
}

impl<'a> Expression<'a> {
    pub fn read(&self) -> Result<String, Error> {
        let (handle, reader) = pipe_with_reader_thread();
        let mut context = IoContext::new();
        context.stdout = handle;
        let status = try!(self.inner.exec(context));
        let stdout_vec = try!(reader.join().unwrap());
        if !status.success() {
            return Err(Error::Status(Output {
                status: status,
                stdout: stdout_vec,
                stderr: Vec::new(),
            }));
        }
        let stdout_string = try!(std::str::from_utf8(&stdout_vec))
                                .trim_right_matches('\n')
                                .to_owned();
        Ok(stdout_string)
    }

    pub fn pipe<T: Borrow<Expression<'a>>>(&self, right: T) -> Expression<'a> {
        Expression {
            inner: Arc::new(ExpressionInner::Exec(ExecutableExpression::Pipe(self.clone(),
                                                                             right.borrow()
                                                                                  .clone()))),
        }
    }

    pub fn then<T: Borrow<Expression<'a>>>(&self, right: T) -> Expression<'a> {
        Expression {
            inner: Arc::new(ExpressionInner::Exec(ExecutableExpression::Then(self.clone(),
                                                                             right.borrow()
                                                                                  .clone()))),
        }
    }

    // TODO: Do clever things with custom traits here instead.
    pub fn stdin_path<T: AsRef<Path> + Send + Sync + 'a>(&self, arg: T) -> Self {
        Expression {
            inner:
                Arc::new(ExpressionInner::Io(IoRedirect::Stdin(InputRedirect::Path(Box::new(arg))),
                                             self.clone())),
        }
    }

    pub fn stdin_file<T: Borrow<File> + Send + Sync + 'a>(&self, arg: T) -> Self {
        Expression {
            inner:
                Arc::new(ExpressionInner::Io(IoRedirect::Stdin(InputRedirect::File(Box::new(arg))),
                                             self.clone())),
        }
    }

    pub fn stdin_bytes<T: AsRef<[u8]> + Send + Sync + 'a>(&self, arg: T) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stdin(InputRedirect::Bytes(Box::new(arg))), self.clone())),
        }
    }

    pub fn stdin_null(&self) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stdin(InputRedirect::Null),
                                                self.clone())),
        }
    }

    pub fn stdout_path<T: AsRef<Path> + Send + Sync + 'a>(&self, arg: T) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stdout(OutputRedirect::Path(Box::new(arg))),
                                                          self.clone())),
        }
    }

    pub fn stdout_file<T: Borrow<File> + Send + Sync + 'a>(&self, arg: T) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stdout(OutputRedirect::File(Box::new(arg))),
                                                          self.clone())),
        }
    }

    pub fn stdout_null(&self) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stdout(OutputRedirect::Null),
                                                self.clone())),
        }
    }

    pub fn stdout_to_stderr(&self) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stdout(OutputRedirect::Stderr),
                                                self.clone())),
        }
    }

    pub fn stderr_path<T: AsRef<Path> + Send + Sync + 'a>(&self, arg: T) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stderr(OutputRedirect::Path(Box::new(arg))),
                                                          self.clone())),
        }
    }

    pub fn stderr_file<T: Borrow<File> + Send + Sync + 'a>(&self, arg: T) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stderr(OutputRedirect::File(Box::new(arg))),
                                                          self.clone())),
        }
    }

    pub fn stderr_null(&self) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stderr(OutputRedirect::Null),
                                                self.clone())),
        }
    }

    pub fn stderr_to_stdout(&self) -> Self {
        Expression {
            inner: Arc::new(ExpressionInner::Io(IoRedirect::Stderr(OutputRedirect::Stdout),
                                                self.clone())),
        }
    }
}

#[derive(Debug)]
enum ExpressionInner<'a> {
    Exec(ExecutableExpression<'a>),
    Io(IoRedirect<'a>, Expression<'a>),
}

impl<'a> ExpressionInner<'a> {
    fn exec(&self, parent_context: IoContext) -> io::Result<ExitStatus> {
        match self {
            &ExpressionInner::Exec(ref executable) => executable.exec(parent_context),
            &ExpressionInner::Io(ref ioarg, ref expr) => {
                ioarg.with_redirected_context(parent_context, |context| expr.inner.exec(context))
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
    fn exec(&self, context: IoContext) -> io::Result<ExitStatus> {
        match self {
            &ExecutableExpression::ArgvCommand(ref argv) => exec_argv(argv, context),
            &ExecutableExpression::ShCommand(ref command) => exec_sh(command, context),
            &ExecutableExpression::Pipe(ref left, ref right) => exec_pipe(left, right, context),
            &ExecutableExpression::Then(ref left, ref right) => exec_then(left, right, context),
        }
    }
}

fn exec_argv<T: AsRef<OsStr>>(argv: &[T], context: IoContext) -> io::Result<ExitStatus> {
    let mut command = Command::new(&argv[0]);
    command.args(&argv[1..]);
    command.stdin(context.stdin.into_stdio());
    command.stdout(context.stdout.into_stdio());
    command.stderr(context.stderr.into_stdio());
    command.status()
}

fn exec_sh<T: AsRef<OsStr>>(command: T, context: IoContext) -> io::Result<ExitStatus> {
    // TODO: What shell should we be using here, really?
    // TODO: Figure out how cmd.Exec works on Windows.
    let mut argv = Vec::new();
    argv.push("bash".as_ref());
    argv.push("-c".as_ref());
    argv.push(command.as_ref());
    exec_argv(&argv, context)
}

fn exec_pipe(left: &Expression, right: &Expression, context: IoContext) -> io::Result<ExitStatus> {
    let (read_pipe, write_pipe) = pipe::open_pipe();
    let left_context = IoContext {
        stdin: context.stdin,
        stdout: write_pipe,
        stderr: context.stderr.clone(),
    };
    let right_context = IoContext {
        stdin: read_pipe,
        stdout: context.stdout,
        stderr: context.stderr,
    };

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
    let status = try!(left.inner.exec(context.clone()));
    if !status.success() {
        Ok(status)
    } else {
        right.inner.exec(context)
    }
}

#[derive(Debug)]
enum IoRedirect<'a> {
    Stdin(InputRedirect<'a>),
    Stdout(OutputRedirect<'a>),
    Stderr(OutputRedirect<'a>),
}

impl<'a> IoRedirect<'a> {
    fn with_redirected_context<F, T>(&self, parent_context: IoContext, inner: F) -> io::Result<T>
        where F: FnOnce(IoContext) -> io::Result<T>
    {
        crossbeam::scope(|scope| {
            let mut context = parent_context;  // move it into the closure
            let mut maybe_stdin_thread = None;
            // Perform the redirect.
            match self {
                &IoRedirect::Stdin(ref redir) => {
                    let (handle, maybe_thread) = try!(redir.open_handle_maybe_thread(scope));
                    maybe_stdin_thread = maybe_thread;
                    context.stdin = handle;
                }
                &IoRedirect::Stdout(ref redir) => {
                    context.stdout = try!(redir.open_handle(&context.stdout, &context.stderr));
                }
                &IoRedirect::Stderr(ref redir) => {
                    context.stderr = try!(redir.open_handle(&context.stdout, &context.stderr));
                }
            }

            // Run the inner closure.
            let ret = try!(inner(context));

            // Join the input thread, if any.
            if let Some(thread) = maybe_stdin_thread {
                try!(thread.join());
            }

            Ok(ret)
        })
    }
}

enum InputRedirect<'a> {
    Null,
    Path(Box<AsRef<Path> + Send + Sync + 'a>),
    File(Box<Borrow<File> + Send + Sync + 'a>),
    Bytes(Box<AsRef<[u8]> + Send + Sync + 'a>),
}

impl<'a, 'b> InputRedirect<'a>
    where 'a: 'b
{
    fn open_handle_maybe_thread(&'a self,
                                scope: &crossbeam::Scope<'b>)
                                -> io::Result<(pipe::Handle, Option<WriterThreadJoiner>)> {
        let mut maybe_thread = None;
        let handle = match self {
            &InputRedirect::Null => pipe::Handle::from_file(try!(File::open("/dev/null"))),  // TODO: Windows
            &InputRedirect::Path(ref p) => pipe::Handle::from_file(try!(File::open(p.as_ref()))),
            &InputRedirect::File(ref f) => pipe::Handle::dup_file((**f).borrow()),
            &InputRedirect::Bytes(ref v) => {
                let (handle, thread) = pipe_with_writer_thread(v.as_ref().as_ref(), scope);
                maybe_thread = Some(thread);
                handle
            }
        };
        Ok((handle, maybe_thread))
    }
}

impl<'a> fmt::Debug for InputRedirect<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &InputRedirect::Null => write!(f, "Null"),
            &InputRedirect::Path(ref p) => write!(f, "Path({:?})", p.as_ref().as_ref()),
            &InputRedirect::File(_) => write!(f, "File(<file>)"),
            &InputRedirect::Bytes(ref b) => {
                let bytes = b.as_ref().as_ref();
                let maybe_str = std::str::from_utf8(bytes);
                if let Ok(s) = maybe_str {
                    write!(f, "Bytes({:?})", s)
                } else {
                    write!(f, "Bytes({:?})", bytes)
                }
            }
        }
    }
}

enum OutputRedirect<'a> {
    Null,
    Stdout,
    Stderr,
    Path(Box<AsRef<Path> + Send + Sync + 'a>),
    File(Box<Borrow<File> + Send + Sync + 'a>),
}

impl<'a> OutputRedirect<'a> {
    fn open_handle(&self,
                   inherited_stdout: &pipe::Handle,
                   inherited_stderr: &pipe::Handle)
                   -> io::Result<pipe::Handle> {
        Ok(match self {
            &OutputRedirect::Null => pipe::Handle::from_file(try!(File::create("/dev/null"))),  // TODO: Windows
            &OutputRedirect::Stdout => inherited_stdout.clone(),
            &OutputRedirect::Stderr => inherited_stderr.clone(),
            &OutputRedirect::Path(ref p) => pipe::Handle::from_file(try!(File::create(p.as_ref()))),
            &OutputRedirect::File(ref f) => pipe::Handle::dup_file((**f).borrow()),
        })
    }
}

impl<'a> fmt::Debug for OutputRedirect<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &OutputRedirect::Null => write!(f, "Null"),
            &OutputRedirect::Stdout => write!(f, "Stdout"),
            &OutputRedirect::Stderr => write!(f, "Stderr"),
            &OutputRedirect::Path(ref p) => write!(f, "Path({:?})", p.as_ref().as_ref()),
            &OutputRedirect::File(_) => write!(f, "File(<file>)"),
        }
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
#[derive(Clone, Debug)]
pub struct IoContext {
    stdin: pipe::Handle,
    stdout: pipe::Handle,
    stderr: pipe::Handle,
}

impl IoContext {
    fn new() -> IoContext {
        IoContext {
            stdin: pipe::Handle::stdin(),
            stdout: pipe::Handle::stdout(),
            stderr: pipe::Handle::stderr(),
        }
    }
}

fn pipe_with_reader_thread() -> (pipe::Handle, JoinHandle<io::Result<Vec<u8>>>) {
    let (read_pipe, write_pipe) = pipe::open_pipe();
    let thread = std::thread::spawn(move || {
        let mut read_file = read_pipe.into_file();
        let mut output = Vec::new();
        try!(read_file.read_to_end(&mut output));
        Ok(output)
    });
    (write_pipe, thread)
}

type WriterThreadJoiner = crossbeam::ScopedJoinHandle<io::Result<()>>;

fn pipe_with_writer_thread<'a>(input: &'a [u8],
                               scope: &crossbeam::Scope<'a>)
                               -> (pipe::Handle, WriterThreadJoiner) {
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

    use super::*;
    use std::io::prelude::*;
    use std::io::SeekFrom;

    #[test]
    fn test_cmd() {
        let output = cmd(&["echo", "hi"]).read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_sh() {
        let output = sh("echo hi").read().unwrap();
        assert_eq!("hi", output);
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
        let expr = sh("sed s/f/g/").stdin_bytes(b"foo");
        let output = expr.read().unwrap();
        assert_eq!("goo", output);
    }

    #[test]
    fn test_null() {
        let expr = cmd(&["cat"]).stdin_null().stdout_null().stderr_null();
        let output = expr.read().unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_path() {
        let mut input_file = tempfile::NamedTempFile::new().unwrap();
        let output_file = tempfile::NamedTempFile::new().unwrap();
        input_file.write_all(b"foo").unwrap();
        let expr = sh("sed s/o/a/g").stdin_path(input_file.path()).stdout_path(output_file.path());
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
            expr.stdin_bytes(mystr)
        }

        let c = cmd(&["cat"]);
        let c_with_input = with_input(&c);
        let output = c_with_input.read().unwrap();
        assert_eq!("I own this: foo", output);
    }

    #[test]
    fn test_stderr_to_stdout() {
        let command = sh("echo hi >&2").stderr_to_stdout();
        let output = command.read().unwrap();
        assert_eq!("hi", output);
    }

    #[test]
    fn test_file() {
        let mut temp = tempfile::NamedTempFile::new().unwrap();
        temp.write_all(b"example").unwrap();
        temp.seek(SeekFrom::Start(0)).unwrap();
        let expr = cmd(&["cat"]).stdin_file(temp.as_ref());
        let output = expr.read().unwrap();
        assert_eq!(output, "example");
    }
}
