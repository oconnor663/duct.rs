use std::ffi::{OsStr, OsString};
use std::process::{Command, ExitStatus};
use std::path::{Path, PathBuf};
use std::io;
use std::fs::File;
use std::os::unix::io::{FromRawFd, IntoRawFd};

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

    pub fn run(&self) -> Result<CommandOutput, DuctError> {
        // Create a Command and add the args.
        let mut command = Command::new(&self.argv[0]);
        command.args(&self.argv[1..]);
        if let Some(ref path) = self.stdout {
            let file = try!(File::create(path));
            command.stdout(unsafe {
                FromRawFd::from_raw_fd(file.into_raw_fd())
            });
        }
        let exit_status = try!(command.status());
        Ok(CommandOutput{
            stdout: None,
            stderr: None,
            status: exit_status,
        })
    }
}

#[derive(Debug, Clone)]
pub struct CommandOutput {
    pub stdout: Option<Vec<u8>>,
    pub stderr: Option<Vec<u8>>,
    pub status: ExitStatus,
}

#[derive(Debug)]
pub enum DuctError {
    Io(io::Error),
    Status(CommandOutput),
}

impl From<io::Error> for DuctError {
    fn from(err: io::Error) -> DuctError {
        DuctError::Io(err)
    }
}

#[cfg(test)]
mod test {
    use super::ArgvCommand;
    use std::fs::File;
    use std::io::prelude::*;

    #[test]
    fn test_run() {
        let result = ArgvCommand::new("true").arg("foo").arg("bar").run();
        assert!(result.unwrap().status.success());
    }

    #[test]
    fn test_stdout() {
        let path = "/tmp/cargo_test_file";
        let result = ArgvCommand::new("echo").arg("hi").stdout(path).run();
        assert!(result.unwrap().status.success());
        let mut contents = String::new();
        File::open(path).unwrap().read_to_string(&mut contents).unwrap();
        assert_eq!(contents, "hi\n");
    }
}
