extern crate libc;

use std::io;

use super::{Expression, ExpressionInner, Handle, HandleInner, IoExpressionInner, PipeHandle,
            ThenHandle};
use shared_child::unix::SharedChildExt;

pub trait HandleExt {
    /// Send a signal to all child processes running under this expression.
    ///
    /// # Caveat
    ///
    /// In the case of a `then` expression where the left expression is unchecked and dies from the
    /// signal, then the right expression will start anyway. If the intention is to stop the entire
    /// expression then the `kill` method should be used instead.
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()>;
}

impl HandleExt for Handle {
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()> {
        self.inner.send_signal(signal)
    }
}

impl HandleExt for HandleInner {
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()> {
        match *self {
            HandleInner::Child(ref child_handle) => child_handle.child.send_signal(signal),
            HandleInner::Pipe(ref pipe_handle) => pipe_handle.send_signal(signal),
            HandleInner::Then(ref then_handle) => then_handle.send_signal(signal),
            HandleInner::Input(ref input_handle) => input_handle.inner_handle.send_signal(signal),
            HandleInner::Unchecked(ref inner_handle) => inner_handle.send_signal(signal),
        }
    }
}

impl HandleExt for PipeHandle {
    /// Signals both parts of this `pipe` expression. Returns an error if signalling one of the
    /// expressions returned an error.
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()> {
        let left_result = self.left_handle.send_signal(signal);
        let right_result = self.right_start_result
            .as_ref()
            .map(|right_handle| right_handle.send_signal(signal))
            .unwrap_or(Ok(()));
        left_result.and(right_result)
    }
}

impl HandleExt for ThenHandle {
    /// Signals the running part of this `then` expression.
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()> {
        match self.shared_state.right_cell.borrow() {
            Some(&Ok(ref right_handle)) => right_handle.send_signal(signal),
            Some(&Err(_)) => Ok(()),
            None => self.shared_state.left_handle.send_signal(signal),
        }
    }
}

pub trait ExpressionExt {
    /// Sets the child process's user id. This translates to a `setuid` call in the child
    /// process. Failure in the `setuid` call will cause the spawn to fail.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate duct;
    /// # #[cfg(unix)] use duct::unix::ExpressionExt;
    /// # fn main() {
    /// # if cfg!(unix) {
    /// let cmd = cmd!("id").uid(123).run();
    /// let err = cmd.err().unwrap();
    /// // Changing uid is not allowed unless running as root
    /// assert_eq!(err.kind(), std::io::ErrorKind::PermissionDenied);
    /// # }
    /// # }
    /// ```
    fn uid(&self, uid: u32) -> Expression;

    /// Similar to `uid`, but sets the group id of the child process. This has
    /// the same semantics as the `uid` field.
    ///
    /// # Example
    ///
    /// ```
    /// # #[macro_use] extern crate duct;
    /// # #[cfg(unix)] use duct::unix::ExpressionExt;
    /// # fn main() {
    /// # if cfg!(unix) {
    /// let cmd = cmd!("id").gid(123).run();
    /// let err = cmd.err().unwrap();
    /// // Changing gid is not allowed unless running as root
    /// assert_eq!(err.kind(), std::io::ErrorKind::PermissionDenied);
    /// # }
    /// # }
    /// ```
    fn gid(&self, gid: u32) -> Expression;
}

impl ExpressionExt for Expression {
    fn uid(&self, uid: u32) -> Expression {
        Expression::new(ExpressionInner::Io(
            IoExpressionInner::Uid(uid),
            self.clone(),
        ))
    }

    fn gid(&self, gid: u32) -> Expression {
        Expression::new(ExpressionInner::Io(
            IoExpressionInner::Gid(gid),
            self.clone(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use test::*;
    use cmd;
    use super::{libc, HandleExt};

    use std::os::unix::process::ExitStatusExt;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_send_signal_from_other_thread() {
        let sleep_cmd = cmd(path_to_exe("sleep"), &["1000000"]);
        let handle = Arc::new(sleep_cmd.unchecked().start().unwrap());
        let handle_clone = handle.clone();

        thread::spawn(move || handle_clone.send_signal(libc::SIGABRT).unwrap());
        let status = handle.wait().unwrap();

        assert_eq!(Some(libc::SIGABRT), status.status.signal());
    }

    #[test]
    fn test_send_signal_to_pipe() {
        let sleep_cmd = cmd(path_to_exe("sleep"), &["1000000"]);
        let handle = sleep_cmd
            .pipe(sleep_cmd.clone())
            .unchecked()
            .start()
            .unwrap();
        handle.send_signal(libc::SIGABRT).unwrap();
        let status = handle.output().unwrap();
        assert_eq!(Some(libc::SIGABRT), status.status.signal());
    }

    /// Tests the caveat explained in the documentation for `send_signal`
    #[test]
    fn test_signal_then_expression() {
        let sleep_cmd = cmd(path_to_exe("sleep"), &["1000000"]);
        let handle = sleep_cmd
            .unchecked()
            .then(true_cmd())
            .unchecked()
            .start()
            .unwrap();
        handle.send_signal(libc::SIGTERM).unwrap();
        let status = handle.wait().unwrap();
        // Since the sleep is unchecked the `then` expression will happily start the second
        // expression and return the status of it upon completion.
        assert_eq!(None, status.status.signal());
        assert!(status.status.success());
    }
}
