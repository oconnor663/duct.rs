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
    fn exec(&self, context: IoContext) -> io::Result<ExitStatus>;

    fn get_ioargs(&mut self) -> &mut IoArgs;

    fn run(&self) -> Result<Output, Error> {
        let context = IoContext {
            stdin: CloneableStdio::Inherit,
            stdout: CloneableStdio::Inherit,
            stderr: CloneableStdio::Inherit,
        };
        let status = try!(self.exec(context));
        Ok(Output{
            status: status,
            stdout: Vec::new(),
            stderr: Vec::new(),
        })
    }

    fn read(&self) -> Result<String, Error> {
        let (stdout, stdout_reader) = pipe_with_reader_thread();
        let context = IoContext {
            stdin: CloneableStdio::Inherit,
            stdout: CloneableStdio::Handle(stdout),
            stderr: CloneableStdio::Inherit,
        };
        let status = try!(self.exec(context));
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

    fn stdin(&mut self, path: &AsRef<Path>) -> &mut Self {
        self.get_ioargs().stdin = Some(path.as_ref().to_owned());
        self
    }

    fn stdout(&mut self, path: &AsRef<Path>) -> &mut Self {
        self.get_ioargs().stdout = Some(path.as_ref().to_owned());
        self
    }

    fn stderr(&mut self, path: &AsRef<Path>) -> &mut Self {
        self.get_ioargs().stderr = Some(path.as_ref().to_owned());
        self
    }
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
    fn exec(&self, context: IoContext) -> io::Result<ExitStatus> {
        let new_context = try!(self.ioargs.update_context(context));
        let IoContext{stdin, stdout, stderr} = new_context;
        // Create a Command and add the args.
        let mut command = Command::new(&self.argv[0]);
        command.args(&self.argv[1..]);
        command.stdin(stdin.to_stdio());
        command.stdout(stdout.to_stdio());
        command.stderr(stderr.to_stdio());
        Ok(try!(command.status()))
    }

    fn get_ioargs(&mut self) -> &mut IoArgs {
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
    fn exec(&self, context: IoContext) -> io::Result<ExitStatus> {
        let new_context = try!(self.ioargs.update_context(context));
        let IoContext{stdin, stdout, stderr} = new_context;
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
        let left_clone = self.left.clone();
        let left_thread = std::thread::spawn(move || {
            left_clone.exec(left_context)
        });
        let right_status = self.right.exec(right_context);
        let left_status = left_thread.join().unwrap();
        match right_status {
            Err(_) => right_status,
            _ => left_status,
        }
    }

    fn get_ioargs(&mut self) -> &mut IoArgs {
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
    stdin: Option<PathBuf>,
    stdout: Option<PathBuf>,
    stderr: Option<PathBuf>,
}

impl IoArgs {
    fn new() -> IoArgs {
        IoArgs { stdin: None, stdout: None, stderr: None }
    }

    fn update_context(&self, mut context: IoContext) -> Result<IoContext, io::Error> {
        if let Some(ref path) = self.stdin {
            context.stdin = CloneableStdio::Handle(pipe::Handle::from_file(
                try!(File::open(&path))));
        }
        if let Some(ref path) = self.stdout {
            context.stdout = CloneableStdio::Handle(pipe::Handle::from_file(
                try!(File::create(&path))));
        }
        if let Some(ref path) = self.stderr {
            context.stderr = CloneableStdio::Handle(pipe::Handle::from_file(
                try!(File::create(&path))));
        }
        Ok(context)
    }
}

#[derive(Clone, Debug)]
pub struct IoContext {
    stdin: CloneableStdio,
    stdout: CloneableStdio,
    stderr: CloneableStdio,
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
}
