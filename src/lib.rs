extern crate crossbeam;

use std::borrow::Cow;
use std::ffi::{OsStr, OsString};
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::path::Path;
use std::process::{Command, Output, ExitStatus};
use std::thread::JoinHandle;

mod pipe;

pub fn cmd<T: AsRef<OsStr>>(argv: &[T]) -> Expression<'static> {
    let argv_vec = argv.iter().map(|arg| arg.as_ref().to_owned()).collect();
    Expression {
        inner: ExpressionInner::ArgvCommand(argv_vec),
        ioargs: IoArgs::new(),
    }
}

pub fn sh<T: AsRef<OsStr>>(command: T) -> Expression<'static> {
    Expression {
        inner: ExpressionInner::ShCommand(command.as_ref().to_owned()),
        ioargs: IoArgs::new(),
    }
}

pub fn pipe<'a>(left: Expression<'a>, right: Expression<'a>) -> Expression<'a> {
    Expression {
        inner: ExpressionInner::Pipe(Box::new(left), Box::new(right)),
        ioargs: IoArgs::new(),
    }
}

pub fn then<'a>(left: Expression<'a>, right: Expression<'a>) -> Expression<'a> {
    Expression {
        inner: ExpressionInner::Then(Box::new(left), Box::new(right)),
        ioargs: IoArgs::new(),
    }
}

#[derive(Clone, Debug)]
pub struct Expression<'a> {
    inner: ExpressionInner<'a>,
    ioargs: IoArgs<'a>,
}

#[derive(Clone, Debug)]
enum ExpressionInner<'a> {
    ArgvCommand(Vec<OsString>),
    ShCommand(OsString),
    Pipe(Box<Expression<'a>>, Box<Expression<'a>>),
    Then(Box<Expression<'a>>, Box<Expression<'a>>),
}

impl<'a> Expression<'a> {
    pub fn run(&self) -> Result<Output, Error> {
        unreachable!();
    }

    pub fn read(&self) -> Result<String, Error> {
        let (handle, reader) = pipe_with_reader_thread();
        let mut context = IoContext::new();
        context.stdout = handle;
        let status = try!(self.exec(context));
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

    fn exec(&self, parent_context: IoContext) -> io::Result<ExitStatus> {
        self.ioargs.with_child_context(parent_context, |context| {
            match self.inner {
                ExpressionInner::ArgvCommand(ref argv) => exec_argv(argv, context),
                ExpressionInner::ShCommand(ref command) => exec_sh(command, context),
                ExpressionInner::Pipe(ref left, ref right) => exec_pipe(left, right, context),
                ExpressionInner::Then(ref left, ref right) => exec_then(left, right, context),
            }
        })
    }

    pub fn stdin(&mut self, arg: InputArg<'a>) -> &mut Self {
        self.ioargs.stdin = arg;
        self
    }

    pub fn stdout(&mut self, arg: OutputArg<'a>) -> &mut Self {
        self.ioargs.stdout = arg;
        self
    }

    pub fn stderr(&mut self, arg: OutputArg<'a>) -> &mut Self {
        self.ioargs.stderr = arg;
        self
    }
}

fn exec_argv(argv: &Vec<OsString>, context: IoContext) -> io::Result<ExitStatus> {
    let mut command = Command::new(&argv[0]);
    command.args(&argv[1..]);
    command.stdin(context.stdin.to_stdio());
    command.stdout(context.stdout.to_stdio());
    command.stderr(context.stderr.to_stdio());
    command.status()
}

fn exec_sh(command: &OsStr, context: IoContext) -> io::Result<ExitStatus> {
    // TODO: What shell should we be using here, really?
    // TODO: Figure out how cmd.exe works on Windows.
    let mut argv = Vec::new();
    argv.push("bash".into());
    argv.push("-c".into());
    argv.push(command.to_owned());
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
        let left_joiner = scope.spawn(|| left.exec(left_context));
        let right_result = right.exec(right_context);
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
    let status = try!(left.exec(context.clone()));
    if !status.success() {
        Ok(status)
    } else {
        right.exec(context)
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

// IoArgs store the redirections and other settings associated with an expression. At execution
// time, IoArgs are used to modify an IoContext, which contains the actual pipes that child process
#[derive(Clone, Debug)]
struct IoArgs<'a> {
    stdin: InputArg<'a>,
    stdout: OutputArg<'a>,
    stderr: OutputArg<'a>,
}

impl<'a> IoArgs<'a> {
    fn new() -> IoArgs<'static> {
        IoArgs {
            stdin: InputArg::Inherit,
            stdout: OutputArg::Inherit,
            stderr: OutputArg::Inherit,
        }
    }

    fn with_child_context<F, T>(&self, parent_context: IoContext, inner: F) -> io::Result<T>
        where F: FnOnce(IoContext) -> io::Result<T>
    {
        crossbeam::scope(|scope| {
            let parent_context = parent_context;  // move it into the closure
            let (stdin, maybe_stdin_thread) = try!(self.stdin
                                                       .update_handle(parent_context.stdin, scope));
            let stdout = try!(self.stdout.update_handle(parent_context.stdout));
            let stderr = try!(self.stderr.update_handle(parent_context.stderr));
            let (stdout, stderr) = apply_swaps(stdout, stderr, &self.stdout, &self.stderr);

            let child_context = IoContext {
                stdin: stdin,
                stdout: stdout,
                stderr: stderr,
            };

            let ret = try!(inner(child_context));

            if let Some(thread) = maybe_stdin_thread {
                try!(thread.join());
            }

            Ok(ret)
        })
    }
}

// returns (new_stdout, new_stderr)
fn apply_swaps(stdout_handle: pipe::Handle,
               stderr_handle: pipe::Handle,
               stdout_arg: &OutputArg,
               stderr_arg: &OutputArg)
               -> (pipe::Handle, pipe::Handle) {
    // TODO: These clones are a little excessive.
    let new_stdout = if let &OutputArg::Stderr = stdout_arg {
        stderr_handle.clone()
    } else {
        stdout_handle.clone()
    };
    let new_stderr = if let &OutputArg::Stdout = stderr_arg {
        stdout_handle.clone()
    } else {
        stderr_handle.clone()
    };
    (new_stdout, new_stderr)
}

#[derive(Clone, Debug)]
pub enum InputArg<'a> {
    Inherit,
    Null,
    Path(Cow<'a, Path>),
    Bytes(Cow<'a, [u8]>),
}

impl<'a> InputArg<'a> {
    fn update_handle(&'a self,
                     parent_handle: pipe::Handle,
                     scope: &crossbeam::Scope<'a>)
                     -> io::Result<(pipe::Handle, Option<WriterThreadJoiner>)> {
        let mut maybe_thread = None;
        let handle = match self {
            &InputArg::Inherit => parent_handle,
            &InputArg::Null => pipe::Handle::from_file(try!(File::open("/dev/null"))),  // TODO: Windows
            &InputArg::Path(ref p) => pipe::Handle::from_file(try!(File::open(&p))),
            &InputArg::Bytes(ref v) => {
                let (handle, thread) = pipe_with_writer_thread(v, scope);
                maybe_thread = Some(thread);
                handle
            }
        };
        Ok((handle, maybe_thread))
    }
}

// TODO: stdout/stderr swaps
#[derive(Clone, Debug)]
pub enum OutputArg<'a> {
    Inherit,
    Null,
    Stdout,
    Stderr,
    Path(Cow<'a, Path>),
}

impl<'a> OutputArg<'a> {
    fn update_handle(&self, parent_handle: pipe::Handle) -> io::Result<pipe::Handle> {
        let handle = match self {
            // Stdout and Stderr are no-ops here, but with_child_context interprets them. This is
            // because they refer to the *child's* stdout/stderr, with other redirections already
            // applied, rather than to the parent's.
            &OutputArg::Inherit | &OutputArg::Stdout | &OutputArg::Stderr => parent_handle,
            &OutputArg::Null => pipe::Handle::from_file(try!(File::create("/dev/null"))),  // TODO: Windows
            &OutputArg::Path(ref p) => pipe::Handle::from_file(try!(File::create(&p))),
        };
        Ok(handle)
    }
}

// An IoContext represents the file descriptors child processes are talking to at execution time.
// It's initialized in run(), with dups of the stdin/stdout/stderr pipes, and then passed down to
// sub-expressions. Compound expressions will clone() it, and pipes/redirections will modify it
// according to their IoArgs.
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
        let mut read_file = read_pipe.to_file();
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
        let mut write_file = write_pipe.to_file();
        try!(write_file.write_all(&input));
        Ok(())
    });
    (read_pipe, thread)
}

#[cfg(test)]
mod test {
    extern crate tempfile;

    use super::*;
    use std::borrow::Cow;
    use std::io::prelude::*;

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
        let output = pipe(sh("echo hi"), sh("sed s/i/o/")).read().unwrap();
        assert_eq!("ho", output);
    }

    #[test]
    fn test_then() {
        let output = then(sh("echo -n hi"), sh("echo lo")).read().unwrap();
        assert_eq!("hilo", output);
    }

    #[test]
    fn test_input() {
        let mut expr = sh("sed s/f/g/");
        expr.stdin(InputArg::Bytes(Cow::Borrowed(b"foo")));
        let output = expr.read().unwrap();
        assert_eq!("goo", output);
    }

    #[test]
    fn test_null() {
        let mut expr = cmd(&["cat"]);
        expr.stdin(InputArg::Null);
        expr.stdout(OutputArg::Null);
        let output = expr.read().unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_path() {
        let mut input_file = tempfile::NamedTempFile::new().unwrap();
        let mut output_file = tempfile::NamedTempFile::new().unwrap();
        println!("Here are the paths: {:?} {:?}",
                 input_file.path(),
                 output_file.path());
        input_file.write_all(b"foo").unwrap();
        let mut expr = sh("sed s/o/a/g");
        expr.stdin(InputArg::Path(Cow::Owned(input_file.path().to_owned())));
        expr.stdout(OutputArg::Path(Cow::Owned(output_file.path().to_owned())));
        let output = expr.read().unwrap();
        assert_eq!("", output);
        let mut file_output = String::new();
        output_file.read_to_string(&mut file_output).unwrap();
        assert_eq!("faa", file_output);
    }

    #[test]
    fn test_owned_input() {
        fn set_input(expr: &mut Expression) {
            let mystr = format!("I own this: {}", "foo");
            // This would be a lifetime error if we tried to use &mystr.
            expr.stdin(InputArg::Bytes(Cow::Owned(mystr.into_bytes())));
        }

        let mut c = cmd(&["cat"]);
        set_input(&mut c);
        let output = c.read().unwrap();
        assert_eq!("I own this: foo", output);
    }

    #[test]
    fn test_stderr_to_stdout() {
        let mut command = sh("echo hi >&2");
        command.stderr(OutputArg::Stdout);
        let output = command.read().unwrap();
        assert_eq!("hi", output);
    }
}
