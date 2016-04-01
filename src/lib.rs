use std::ffi::{OsStr, OsString};
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::path::PathBuf;
use std::process::{Command, Output, ExitStatus};
use std::thread::JoinHandle;

mod pipe;

pub fn cmd<T: AsRef<OsStr>>(argv: &[T]) -> Expression {
    let argv_vec = argv.iter().map(|arg| arg.as_ref().to_owned()).collect();
    Expression {
        inner: ExpressionInner::ArgvCommand(argv_vec),
        ioargs: IoArgs::new(),
    }
}

pub fn sh<T: AsRef<OsStr>>(command: T) -> Expression {
    Expression {
        inner: ExpressionInner::ShCommand(command.as_ref().to_owned()),
        ioargs: IoArgs::new(),
    }
}

pub fn pipe(left: Expression, right: Expression) -> Expression {
    Expression {
        inner: ExpressionInner::Pipe(Box::new(left), Box::new(right)),
        ioargs: IoArgs::new(),
    }
}

pub fn then(left: Expression, right: Expression) -> Expression {
    Expression {
        inner: ExpressionInner::Then(Box::new(left), Box::new(right)),
        ioargs: IoArgs::new(),
    }
}

#[derive(Clone, Debug)]
pub struct Expression {
    // TODO: Make these private.
    pub inner: ExpressionInner,
    pub ioargs: IoArgs,
}

// TODO: Make this private.
#[derive(Clone, Debug)]
pub enum ExpressionInner {
    ArgvCommand(Vec<OsString>),
    ShCommand(OsString),
    Pipe(Box<Expression>, Box<Expression>),
    Then(Box<Expression>, Box<Expression>),
}

impl Expression {
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
    // TODO: Use a scoped thread here, to avoid this stupid clone.
    let left_expression_clone = left.clone();
    let thread = std::thread::spawn(move || left_expression_clone.exec(left_context));
    let right_status = try!(right.exec(right_context));
    let left_status = try!(thread.join().unwrap());
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
// TODO: Make this private.
#[derive(Clone, Debug)]
pub struct IoArgs {
    stdin: InputArg,
    stdout: OutputArg,
    stderr: OutputArg,
}

impl IoArgs {
    fn new() -> IoArgs {
        IoArgs {
            stdin: InputArg::Inherit,
            stdout: OutputArg::Inherit,
            stderr: OutputArg::Inherit,
        }
    }

    fn with_child_context<F, T>(&self, parent_context: IoContext, inner: F) -> io::Result<T>
        where F: FnOnce(IoContext) -> io::Result<T>
    {
        let (stdin, maybe_stdin_thread) = try!(self.stdin.update_handle(parent_context.stdin));
        let stdout = try!(self.stdout.update_handle(parent_context.stdout));
        let stderr = try!(self.stderr.update_handle(parent_context.stderr));
        let child_context = IoContext {
            stdin: stdin,
            stdout: stdout,
            stderr: stderr,
        };

        let result = try!(inner(child_context));

        if let Some(thread) = maybe_stdin_thread {
            try!(thread.join().unwrap());
        }

        Ok(result)
    }
}

#[derive(Clone, Debug)]
enum InputArg {
    Inherit,
    Null,
    Path(PathBuf),
    Bytes(Vec<u8>),
}

impl InputArg {
    fn update_handle(&self,
                     parent_handle: pipe::Handle)
                     -> io::Result<(pipe::Handle, Option<JoinHandle<io::Result<()>>>)> {
        let mut maybe_thread = None;
        let handle = match self {
            &InputArg::Inherit => parent_handle,
            &InputArg::Null => pipe::Handle::from_file(try!(File::open("/dev/null"))),  // TODO: Windows
            &InputArg::Path(ref p) => pipe::Handle::from_file(try!(File::open(&p))),
            &InputArg::Bytes(ref v) => {
                // TODO: figure out a way to get rid of this clone
                let (handle, thread) = pipe_with_writer_thread(v.clone());
                maybe_thread = Some(thread);
                handle
            }
        };
        Ok((handle, maybe_thread))
    }
}

#[derive(  Clone, Debug)]
enum OutputArg {
    Inherit,
    Null,
    Path(PathBuf), // TODO: stdout/stderr swaps
}

impl OutputArg {
    fn update_handle(&self, parent_handle: pipe::Handle) -> io::Result<pipe::Handle> {
        let handle = match self {
            &OutputArg::Inherit => parent_handle,
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

fn pipe_with_writer_thread(input: Vec<u8>) -> (pipe::Handle, JoinHandle<io::Result<()>>) {
    let (read_pipe, write_pipe) = pipe::open_pipe();
    let thread = std::thread::spawn(move || {
        let mut write_file = write_pipe.to_file();
        try!(write_file.write_all(&input));
        Ok(())
    });
    (read_pipe, thread)
}

#[cfg(test)]
mod test {
    use super::{cmd, sh, pipe, then, InputArg, OutputArg};
    use std::fs::File;
    use std::io::prelude::*;
    use std::path::Path;

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
        expr.ioargs.stdin = InputArg::Bytes(b"foo".to_vec());
        let output = expr.read().unwrap();
        assert_eq!("goo", output);
    }

    #[test]
    fn test_null() {
        let mut expr = cmd(&["cat"]);
        expr.ioargs.stdin = InputArg::Null;
        expr.ioargs.stdout = OutputArg::Null;
        let output = expr.read().unwrap();
        assert_eq!("", output);
    }

    #[test]
    fn test_path() {
        let input_path = Path::new("/tmp/duct_file_input");
        let output_path = Path::new("/tmp/duct_file_output");
        File::create(&input_path).unwrap().write_all(b"foo").unwrap();
        let mut expr = sh("sed s/o/a/g");
        expr.ioargs.stdin = InputArg::Path(input_path.to_owned());
        expr.ioargs.stdout = OutputArg::Path(output_path.to_owned());
        let output = expr.read().unwrap();
        assert_eq!("", output);
        let mut file_output = String::new();
        File::open(&output_path).unwrap().read_to_string(&mut file_output).unwrap();
        assert_eq!("faa", file_output);
    }
}
