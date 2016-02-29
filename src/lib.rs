use std::ffi::{OsStr, OsString};
use std::process::Command;

#[derive(Debug, Clone)]
pub struct ArgvCommand {
    argv: Vec<OsString>
}

impl ArgvCommand {
    pub fn new<T: AsRef<OsStr>>(prog: T) -> ArgvCommand {
        ArgvCommand{
            argv: vec![prog.as_ref().to_owned()],
        }
    }

    pub fn arg<T: AsRef<OsStr>>(&mut self, arg: T) -> &mut Self {
        self.argv.push(arg.as_ref().to_owned());
        self
    }

    pub fn run(&self) -> CommandOutput {
        let mut command = Command::new(&self.argv[0]);
        command.args(&self.argv[1..]);
        let exit_status = command.status().unwrap();
        CommandOutput{
            stdout: None,
            stderr: None,
            // TODO: handle processes terminated by signals
            status: exit_status.code().unwrap(),
        }
    }
}

pub struct CommandOutput {
    pub stdout: Option<Vec<u8>>,
    pub stderr: Option<Vec<u8>>,
    pub status: i32,
}

#[cfg(test)]
mod test {
    use super::ArgvCommand;

    #[test]
    fn it_works() {
        let output = ArgvCommand::new("true").arg("foo").arg("bar").run();
        assert_eq!(output.status, 0);
    }
}
