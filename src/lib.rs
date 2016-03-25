use std::ffi::{OsStr, OsString};
use std::fmt::Debug;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio, Output, ExitStatus};
use std::thread::JoinHandle;

mod pipe;

pub trait Expression: Clone + Send + Debug + 'static {
    fn exec_inner(&self, context: IoContext) -> io::Result<ExitStatus>;

    fn get_ioargs(&self) -> &IoArgs;

    fn get_ioargs_mut(&mut self) -> &mut IoArgs;

    fn run(&self) -> Result<Output, Error> {
        let status = try!(apply_ioargs_and_exec(self, IoContext::new()));
        Ok(Output{
            status: status,
            stdout: Vec::new(),
            stderr: Vec::new(),
        })
    }

    fn read(&self) -> Result<String, Error> {
        let (stdout, stdout_reader) = pipe_with_reader_thread();
        let mut context = IoContext::new();
        context.stdout = CloneableStdio::Handle(stdout);
        let status = try!(apply_ioargs_and_exec(self, context));
        let output = Output{
            status: status,
            stdout: try!(stdout_reader.join().unwrap()),
            stderr: Vec::new(),
        };
        if output.status.success() {
            // TODO: should only trim newlines
            Ok(try!(String::from_utf8(output.stdout)).trim_right().to_string())
        } else {
            Err(Error::Status(output))
        }
    }

    fn input<T: AsRef<[u8]>>(&mut self, buf: T) -> &mut Self {
        self.get_ioargs_mut().input = Some(buf.as_ref().to_owned());
        self
    }

    fn stdin<T: AsRef<Path>>(&mut self, path: T) -> &mut Self {
        self.get_ioargs_mut().stdin = Some(path.as_ref().to_owned());
        self
    }

    fn stdout<T: AsRef<Path>>(&mut self, path: T) -> &mut Self {
        self.get_ioargs_mut().stdout = Some(path.as_ref().to_owned());
        self
    }

    fn stderr<T: AsRef<Path>>(&mut self, path: T) -> &mut Self {
        self.get_ioargs_mut().stderr = Some(path.as_ref().to_owned());
        self
    }

    // How will pipe() work here? Can it use <T>?
}

#[derive(Debug, Clone)]
pub struct ArgvCommand {
    argv: Vec<OsString>,
    ioargs: IoArgs,
}

impl ArgvCommand {
    pub fn new<T: AsRef<OsStr>>(prog: T) -> ArgvCommand {
        ArgvCommand{
            argv: vec![prog.as_ref().to_owned()],
            ioargs: IoArgs::new(),
        }
    }

    pub fn arg<T: AsRef<OsStr>>(&mut self, arg: T) -> &mut Self {
        self.argv.push(arg.as_ref().to_owned());
        self
    }
}

impl Expression for ArgvCommand {
    fn exec_inner(&self, context: IoContext) -> io::Result<ExitStatus> {
        let IoContext{stdin, stdout, stderr} = context;
        let mut command = Command::new(&self.argv[0]);
        command.args(&self.argv[1..]);
        command.stdin(stdin.to_stdio());
        command.stdout(stdout.to_stdio());
        command.stderr(stderr.to_stdio());
        command.status()
    }

    fn get_ioargs(&self) -> &IoArgs {
        &self.ioargs
    }

    fn get_ioargs_mut(&mut self) -> &mut IoArgs {
        &mut self.ioargs
    }
}

#[derive(Debug, Clone)]
pub struct Pipe<T: Expression, U: Expression> {
    left: T,
    right: U,
    ioargs: IoArgs,
}

impl<T: Expression, U: Expression> Pipe<T, U> {
    pub fn new(left: &T, right: &U) -> Pipe<T, U> {
        Pipe{left: left.clone(), right: right.clone(), ioargs: IoArgs::new()}
    }
}

impl<T: Expression, U: Expression> Expression for Pipe<T, U> {
    fn exec_inner(&self, context: IoContext) -> io::Result<ExitStatus> {
        // Assemble new IoContexts for the left and the right sides.
        let IoContext{stdin, stdout, stderr} = context;
        let (read_pipe, write_pipe) = pipe::open_pipe();
        let left_context = IoContext{
            stdin: stdin,
            stdout: CloneableStdio::Handle(write_pipe),
            stderr: stderr.clone(),
        };
        let right_context = IoContext{
            stdin: CloneableStdio::Handle(read_pipe),
            stdout: stdout,
            stderr: stderr,
        };

        // Clone the left side, and pass it to a new thread to execute.
        // TODO: Probably use a scoped thread here.
        let left_clone = self.left.clone();
        let left_thread = std::thread::spawn(move || {
            apply_ioargs_and_exec(&left_clone, left_context)
        });

        // Execute the right side in parallel, on this thread.
        let right_status = try!(apply_ioargs_and_exec(&self.right, right_context));

        // Wait for the left to finish, then return the rightmost error, if any.
        let left_status = try!(left_thread.join().unwrap());
        if right_status.success() {
            Ok(left_status)
        } else {
            Ok(right_status)
        }
    }

    fn get_ioargs(&self) -> &IoArgs {
        &self.ioargs
    }

    fn get_ioargs_mut(&mut self) -> &mut IoArgs {
        &mut self.ioargs
    }
}

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Utf8(std::string::FromUtf8Error),
    Status(Output),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::Io(err)
    }
}

impl From<std::string::FromUtf8Error> for Error {
    fn from(err: std::string::FromUtf8Error) -> Error {
        Error::Utf8(err)
    }
}

#[derive(Clone, Debug)]
pub struct IoArgs {
    input: Option<Vec<u8>>,
    stdin: Option<PathBuf>,
    stdout: Option<PathBuf>,
    stderr: Option<PathBuf>,
}

impl IoArgs {
    fn new() -> IoArgs {
        IoArgs { input: None, stdin: None, stdout: None, stderr: None }
    }
}

fn apply_ioargs_and_exec<T: Expression>(expr: &T, mut context: IoContext) -> io::Result<ExitStatus> {
    // Update the IoContext, if any IO arguments are defined for the current expression. This might
    // require spawning a writer thread.
    let ioargs = expr.get_ioargs();
    if let Some(ref path) = ioargs.stdin {
        context.stdin = CloneableStdio::Handle(pipe::Handle::from_file(
            try!(File::open(&path))));
    }
    if let Some(ref path) = ioargs.stdout {
        context.stdout = CloneableStdio::Handle(pipe::Handle::from_file(
            try!(File::create(&path))));
    }
    if let Some(ref path) = ioargs.stderr {
        context.stderr = CloneableStdio::Handle(pipe::Handle::from_file(
            try!(File::create(&path))));
    }
    let mut writer_thread = None;
    if let Some(ref input) = ioargs.input {
        let (pipe_handle, thread_joiner) = pipe_with_writer_thread(input.clone());
        writer_thread = Some(thread_joiner);
        context.stdin = CloneableStdio::Handle(pipe_handle);
    }

    // Execute the expression using the updated IoContext.
    let exec_result = expr.exec_inner(context);

    // If we created a writer thread above, join it, even if the result above is an error.
    // TODO: Suppress closed pipe errors, but pass along others.
    let mut writer_result = Ok(());
    if let Some(join_handle) = writer_thread {
        writer_result = join_handle.join().unwrap();
    }

    let status = try!(exec_result);
    try!(writer_result);
    Ok(status)
}

#[derive(Clone, Debug)]
pub struct IoContext {
    stdin: CloneableStdio,
    stdout: CloneableStdio,
    stderr: CloneableStdio,
}

impl IoContext {
    fn new() -> IoContext {
        IoContext {
            stdin: CloneableStdio::Inherit,
            stdout: CloneableStdio::Inherit,
            stderr: CloneableStdio::Inherit,
        }
    }
}

#[derive(Clone, Debug)]
enum CloneableStdio {
    Inherit,
    Handle(pipe::Handle),
}

impl CloneableStdio {
    fn to_stdio(self) -> Stdio {
        match self {
            CloneableStdio::Inherit => Stdio::inherit(),
            CloneableStdio::Handle(handle) => handle.to_stdio(),
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
    use super::{ArgvCommand, Pipe, Expression};
    use std::fs::File;
    use std::io::prelude::*;
    use std::path::PathBuf;

    fn mktemp() -> PathBuf {
        let output = ArgvCommand::new("mktemp").read().unwrap();
        let path: PathBuf = output.trim().into();
        println!("here's the path we're using: {:?}", path);
        path
    }

    #[test]
    fn test_run() {
        let result = ArgvCommand::new("true").arg("foo").arg("bar").run();
        assert!(result.unwrap().status.success());
    }

    #[test]
    fn test_read() {
        let output = ArgvCommand::new("echo").arg("hi").read().unwrap();
        assert_eq!(output, "hi");
    }

    #[test]
    fn test_stdout() {
        let path = mktemp();
        let result = ArgvCommand::new("echo").arg("hi").stdout(&path).run();
        assert!(result.unwrap().status.success());
        let mut contents = String::new();
        File::open(&path).unwrap().read_to_string(&mut contents).unwrap();
        assert_eq!(contents, "hi\n");
    }

    #[test]
    fn test_pipe() {
        let mut left = ArgvCommand::new("echo");
        left.arg("hi");
        let mut middle = ArgvCommand::new("sed");
        middle.arg("s/i/o/");
        let mut right = ArgvCommand::new("sed");
        right.arg("s/h/j/");
        let pipe = Pipe::new(&left, &Pipe::new(&middle, &right));
        let output = pipe.read().unwrap();
        assert_eq!(output, "jo");
    }

    #[test]
    fn test_input() {
        let output = ArgvCommand::new("cat").input(&"blarg".as_bytes()).read().unwrap();
        assert_eq!(output, "blarg");
    }
}
