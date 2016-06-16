extern crate libc;

use std::os::unix::io::{FromRawFd, IntoRawFd, RawFd};
use std::fs::File;
use std::process::Stdio;

pub fn stdin() -> File {
    dup_or_panic(libc::STDIN_FILENO)
}

pub fn stdout() -> File {
    dup_or_panic(libc::STDOUT_FILENO)
}

pub fn stderr() -> File {
    dup_or_panic(libc::STDERR_FILENO)
}

// (read, write)
// TODO: error handling
pub fn open_pipe() -> (File, File) {
    unsafe {
        let mut pipes = [0, 0];
        let error = libc::pipe(pipes.as_mut_ptr());
        assert_eq!(error, 0);
        make_uninheritable(pipes[0]);
        make_uninheritable(pipes[1]);
        (File::from_raw_fd(pipes[0]), File::from_raw_fd(pipes[1]))
    }
}

pub fn stdio_from_file(f: File) -> Stdio {
    unsafe {
        Stdio::from_raw_fd(f.into_raw_fd())
    }
}

fn dup_or_panic(fd: RawFd) -> File {
    unsafe {
        let new_fd = libc::dup(fd);
        assert!(new_fd >= 0, "dup() returned an error");
        make_uninheritable(new_fd);
        File::from_raw_fd(new_fd)
    }
}

unsafe fn make_uninheritable(fd: RawFd) {
    let ret = libc::ioctl(fd, libc::FIOCLEX);
    assert_eq!(ret, 0);
}

#[cfg(test)]
mod test {
    use super::open_pipe;
    use std::io::prelude::*;

    #[test]
    fn test_pipes() {
        let (r, w) = open_pipe();
        let mut r_clone = r.try_clone().unwrap();
        let mut w_clone = w.try_clone().unwrap();
        drop(w);
        w_clone.write_all(b"some stuff").unwrap();
        drop(w_clone);
        let mut output = Vec::new();
        r_clone.read_to_end(&mut output).unwrap();
    }
}
