//! Unix-only extensions, for sending signals

extern crate libc;

use std::io;

use super::{Handle, HandleInner, PipeHandle, ThenHandle};
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
            None => self.shared_state.left_handle.send_signal(signal)
        }
    }
}
