extern crate libc;

use std::ffi::{OsStr, OsString};
use std::fmt::Debug;
use std::fs::File;
use std::io;
use std::mem;
use std::os::unix::io::{FromRawFd, IntoRawFd, RawFd};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio, Output};

pub trait Expression: Clone + Debug {
    fn exec(&self, context: IoContext) -> Result;

    fn run(&self) -> Result {
        let context = IoContext {
            stdin: CloneableStdio::Inherit,
            stdout: CloneableStdio::Inherit,
            stderr: CloneableStdio::Inherit,
        };
        self.exec(context)
    }
}

#[derive(Debug, Clone)]
pub struct ArgvCommand {
    argv: Vec<OsString>,
    stdout: Option<PathBuf>,
}

impl ArgvCommand {
    pub fn new<T: AsRef<OsStr>>(prog: T) -> ArgvCommand {
        ArgvCommand{
            argv: vec![prog.as_ref().to_owned()],
            stdout: None,
        }
    }

    pub fn arg<T: AsRef<OsStr>>(&mut self, arg: T) -> &mut Self {
        self.argv.push(arg.as_ref().to_owned());
        self
    }

    pub fn stdout<T: AsRef<Path>>(&mut self, path: T) -> &mut Self {
        self.stdout = Some(path.as_ref().to_owned());
        self
    }
}

impl Expression for ArgvCommand {
    fn exec(&self, context: IoContext) -> Result {
        let IoContext{stdin, stdout, stderr} = context;
        // Create a Command and add the args.
        let mut command = Command::new(&self.argv[0]);
        command.args(&self.argv[1..]);
        command.stdin(stdin.to_stdio());
        command.stdout(stdout.to_stdio());
        command.stderr(stderr.to_stdio());
        if let Some(ref path) = self.stdout {
            let file = try!(File::create(path));
            command.stdout(unsafe {
                FromRawFd::from_raw_fd(file.into_raw_fd())
            });
        }
        let exit_status = try!(command.status());
        Ok(Output{
            stdout: Vec::new(),
            stderr: Vec::new(),
            status: exit_status,
        })
    }
}

#[derive(Debug, Clone)]
pub struct Pipe {
    // TODO: Make this hold any Expression.
    left: ArgvCommand,
    right: ArgvCommand,
}

impl Pipe {
    pub fn new(left: &ArgvCommand, right: &ArgvCommand) -> Pipe {
        Pipe{left: left.clone(), right: right.clone()}
    }
}

impl Expression for Pipe {
    fn exec(&self, context: IoContext) -> Result {
        let IoContext{stdin, stdout, stderr} = context;
        let (read_pipe, write_pipe) = open_pipe();
        let left_context = IoContext{
            stdin: stdin,
            stdout: CloneableStdio::Fd(write_pipe),
            stderr: stderr.clone(),
        };
        let right_context = IoContext{
            stdin: CloneableStdio::Fd(read_pipe),
            stdout: stdout,
            stderr: stderr,
        };
        let left_clone = self.left.clone();
        let left_thread = std::thread::spawn(move || {
            left_clone.exec(left_context)
        });
        let right_result = self.right.exec(right_context);
        let left_result = left_thread.join().unwrap();  // TODO: handle errors here?
        match right_result {
            Err(_) => right_result,
            _ => left_result,
        }
    }
}

pub type Result = std::result::Result<Output, Error>;

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Status(Output),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::Io(err)
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
    Fd(CloneableFd),
}

impl CloneableStdio {
    fn to_stdio(self) -> Stdio {
        match self {
            CloneableStdio::Inherit => Stdio::inherit(),
            CloneableStdio::Fd(fd) => unsafe {
                FromRawFd::from_raw_fd(fd.into_raw_fd())
            },
        }
    }
}

#[derive(Debug)]
struct CloneableFd {
    // The struct *owns* this file descriptor, and will close it in drop().
    fd: RawFd,
}

impl Clone for CloneableFd {
    fn clone(&self) -> Self {
        let new_fd = unsafe { libc::dup(self.fd) };
        assert!(new_fd >= 0);
        unsafe { FromRawFd::from_raw_fd(new_fd) }
    }
}

impl FromRawFd for CloneableFd {
    unsafe fn from_raw_fd(fd: RawFd) -> Self {
        CloneableFd{fd: fd}
    }
}

impl IntoRawFd for CloneableFd {
    fn into_raw_fd(self) -> RawFd {
        let fd = self.fd;
        mem::forget(self);  // prevent drop() from closing the fd
        fd
    }
}

impl Drop for CloneableFd {
    fn drop(&mut self) {
        let error = unsafe { libc::close(self.fd) };
        assert_eq!(error, 0);
    }
}

// (read, write)
// TODO: error handling
fn open_pipe() -> (CloneableFd, CloneableFd) {
    unsafe {
        let mut pipes = [0, 0];
        let error = libc::pipe(pipes.as_mut_ptr());
        assert_eq!(error, 0);
        // prevent child processes from inheriting these by default
        for fd in &pipes {
            let ret = libc::ioctl(*fd, libc::FIOCLEX);
            assert_eq!(ret, 0);
        }
        (FromRawFd::from_raw_fd(pipes[0]), FromRawFd::from_raw_fd(pipes[1]))
    }
}

#[cfg(test)]
mod test {
    use super::{ArgvCommand, Pipe, Expression};
    use std::fs::File;
    use std::io::prelude::*;
    use std::path::PathBuf;
    use std::process::Command;
    use std::str::from_utf8;

    fn mktemp() -> PathBuf {
        // TODO: use duct for this :)
        let output = Command::new("mktemp").output().unwrap();
        let path: PathBuf = from_utf8(&output.stdout).unwrap().trim().into();
        println!("here's the path we're using: {:?}", path);
        path
    }

    #[test]
    fn test_run() {
        let result = ArgvCommand::new("true").arg("foo").arg("bar").run();
        assert!(result.unwrap().status.success());
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
        let mut right = ArgvCommand::new("sed");
        right.arg("s/i/o/");
        let path = mktemp();
        right.stdout(&path);
        let pipe = Pipe::new(&left, &right);
        let result = pipe.run();
        assert!(result.unwrap().status.success());
        let mut contents = String::new();
        File::open(&path).unwrap().read_to_string(&mut contents).unwrap();
        assert_eq!(contents, "ho\n");
    }
}
