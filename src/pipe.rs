extern crate libc;

use std::mem;
use std::os::unix::io::{FromRawFd, IntoRawFd, RawFd};
use std::fs::File;
use std::process::Stdio;

#[derive(Debug)]
pub struct Handle {
    // The struct *owns* this file descriptor, and will close it in drop().
    fd: RawFd,
}

impl Handle {
    pub fn to_file(self) -> File {
        unsafe { File::from_raw_fd(self.into_raw_fd()) }
    }

    pub fn to_stdio(self) -> Stdio {
        unsafe { Stdio::from_raw_fd(self.into_raw_fd()) }
    }
}

impl Clone for Handle {
    fn clone(&self) -> Self {
        let new_fd = unsafe { libc::dup(self.fd) };
        assert!(new_fd >= 0);
        unsafe { FromRawFd::from_raw_fd(new_fd) }
    }
}

impl FromRawFd for Handle {
    unsafe fn from_raw_fd(fd: RawFd) -> Self {
        Handle{fd: fd}
    }
}

impl IntoRawFd for Handle {
    fn into_raw_fd(self) -> RawFd {
        let fd = self.fd;
        mem::forget(self);  // prevent drop() from closing the fd
        fd
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        let error = unsafe { libc::close(self.fd) };
        assert_eq!(error, 0);
    }
}

// (read, write)
// TODO: error handling
pub fn open_pipe() -> (Handle, Handle) {
    unsafe {
        let mut pipes = [0, 0];
        let error = libc::pipe(pipes.as_mut_ptr());
        assert_eq!(error, 0);
        // prevent child processes from inheriting these by default
        for fd in &pipes {
            let ret = libc::ioctl(*fd, libc::FIOCLEX);
            assert_eq!(ret, 0);
        }
        (Handle::from_raw_fd(pipes[0]), Handle::from_raw_fd(pipes[1]))
    }
}

#[cfg(test)]
mod test {
    use super::open_pipe;
    use std::io::prelude::*;

    #[test]
    fn it_works() {
        let (r, w) = open_pipe();
        let mut r_file = r.to_file();
        let mut w_file = w.to_file();
        w_file.write_all(b"some stuff").unwrap();
        drop(w_file);
        let mut output = Vec::new();
        r_file.read_to_end(&mut output).unwrap();
    }
}
