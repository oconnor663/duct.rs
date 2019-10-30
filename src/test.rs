use super::{cmd, Expression};
use std;
use std::collections::HashMap;
use std::env;
use std::env::consts::EXE_EXTENSION;
use std::ffi::OsString;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str;
use std::sync::{Arc, Once};
use tempdir::TempDir;

// Include a copy of the sh function, because we have a lot of old tests that
// use it, and it's a lot easier than managing a circular dependency between
// duct and duct_sh.

pub fn sh(command: &'static str) -> Expression {
    let argv = shell_command_argv(command.into());
    cmd(&argv[0], &argv[1..])
}

#[cfg(unix)]
fn shell_command_argv(command: OsString) -> Vec<OsString> {
    vec!["/bin/sh".into(), "-c".into(), command]
}

#[cfg(windows)]
fn shell_command_argv(command: OsString) -> Vec<OsString> {
    let comspec = std::env::var_os("COMSPEC").unwrap_or_else(|| "cmd.exe".into());
    vec![comspec, "/C".into(), command]
}

pub fn path_to_exe(name: &str) -> PathBuf {
    // This project defines some associated binaries for testing, and we shell out to them in
    // these tests. `cargo test` doesn't automatically build associated binaries, so this
    // function takes care of building them explicitly.
    static CARGO_BUILD_ONCE: Once = Once::new();
    CARGO_BUILD_ONCE.call_once(|| {
        let build_status = Command::new("cargo")
            .arg("build")
            .arg("--quiet")
            .status()
            .unwrap();
        assert!(
            build_status.success(),
            "Cargo failed to build associated binaries."
        );
    });

    Path::new("target")
        .join("debug")
        .join(name)
        .with_extension(EXE_EXTENSION)
}

pub fn true_cmd() -> Expression {
    cmd!(path_to_exe("status"), "0")
}

fn false_cmd() -> Expression {
    cmd!(path_to_exe("status"), "1")
}

#[test]
fn test_cmd() {
    let output = cmd!(path_to_exe("echo"), "hi").read().unwrap();
    assert_eq!("hi", output);
}

#[test]
fn test_sh() {
    // Windows compatible.
    let output = sh("echo hi").read().unwrap();
    assert_eq!("hi", output);
}

#[test]
fn test_start() {
    let handle1 = cmd!(path_to_exe("echo"), "hi")
        .stdout_capture()
        .start()
        .unwrap();
    let handle2 = cmd!(path_to_exe("echo"), "lo")
        .stdout_capture()
        .start()
        .unwrap();
    let output1 = handle1.wait().unwrap();
    let output2 = handle2.wait().unwrap();
    assert_eq!("hi", str::from_utf8(&output1.stdout).unwrap().trim());
    assert_eq!("lo", str::from_utf8(&output2.stdout).unwrap().trim());
}

#[test]
fn test_error() {
    let result = false_cmd().run();
    if let Err(err) = result {
        assert_eq!(err.kind(), io::ErrorKind::Other);
    } else {
        panic!("Expected a status error.");
    }
}

#[test]
fn test_unchecked() {
    let unchecked_false = false_cmd().unchecked();
    // Unchecked errors shouldn't cause `run` to return an error.
    let output = unchecked_false
        .pipe(cmd!(path_to_exe("echo"), "waa"))
        .stdout_capture()
        .run()
        .unwrap();
    // The value of the exit code is preserved.
    assert_eq!(1, output.status.code().unwrap());
    assert_eq!("waa", String::from_utf8_lossy(&output.stdout).trim());
}

#[test]
fn test_unchecked_in_pipe() {
    let zero = cmd!(path_to_exe("status"), "0");
    let one = cmd!(path_to_exe("status"), "1");
    let two = cmd!(path_to_exe("status"), "2");

    // Right takes precedence over left.
    let output = one.pipe(two.clone()).unchecked().run().unwrap();
    assert_eq!(2, output.status.code().unwrap());

    // Except that checked on the left takes precedence over unchecked on
    // the right.
    let output = one.pipe(two.unchecked()).unchecked().run().unwrap();
    assert_eq!(1, output.status.code().unwrap());

    // Right takes precedence over the left again if they're both unchecked.
    let output = one
        .unchecked()
        .pipe(two.unchecked())
        .unchecked()
        .run()
        .unwrap();
    assert_eq!(2, output.status.code().unwrap());

    // Except that if the right is a success, the left takes precedence.
    let output = one
        .unchecked()
        .pipe(zero.unchecked())
        .unchecked()
        .run()
        .unwrap();
    assert_eq!(1, output.status.code().unwrap());

    // Even if the right is checked.
    let output = one.unchecked().pipe(zero).unchecked().run().unwrap();
    assert_eq!(1, output.status.code().unwrap());
}

#[test]
fn test_pipe() {
    let output = sh("echo xxx")
        .pipe(cmd!(path_to_exe("x_to_y")))
        .read()
        .unwrap();
    assert_eq!("yyy", output);

    // Check that errors on either side are propagated.
    let result = true_cmd().pipe(false_cmd()).run();
    assert!(result.is_err());

    let result = false_cmd().pipe(true_cmd()).run();
    assert!(result.is_err());
}

#[test]
fn test_pipe_with_kill() {
    // Make sure both sides get killed.
    let sleep_cmd = cmd!(path_to_exe("sleep"), "1000000");
    // Note that we don't use unchecked() here. This tests that kill suppresses
    // exit status errors.
    let handle = sleep_cmd.pipe(sleep_cmd.clone()).start().unwrap();
    handle.kill().unwrap();
    // But calling wait again should be an error, because of the status.
    handle.wait().unwrap_err();
}

#[test]
fn test_pipe_start() {
    let nonexistent_cmd = cmd!(path_to_exe("nonexistent!!!"));
    let sleep_cmd = cmd!(path_to_exe("sleep"), "1000000");

    // Errors starting the left side of a pipe are returned immediately, and
    // the right side is never started.
    nonexistent_cmd.pipe(&sleep_cmd).start().unwrap_err();

    // Errors starting the right side are also returned immediately, and the
    // the left side is killed first.
    sleep_cmd.pipe(nonexistent_cmd).start().unwrap_err();
}

#[test]
fn test_multiple_threads() {
    // Wait on the sleep command in a background thread, while the main thread
    // kills it.
    let sleep_cmd = cmd!(path_to_exe("sleep"), "1000000");
    let handle = Arc::new(sleep_cmd.unchecked().start().unwrap());
    let arc_clone = handle.clone();
    let wait_thread = std::thread::spawn(move || {
        arc_clone.wait().unwrap();
    });
    handle.kill().unwrap();
    wait_thread.join().unwrap();
}

#[test]
fn test_nonblocking_waits() {
    let sleep_cmd = cmd!(path_to_exe("sleep"), "1000000");
    // Make sure pipelines handle try_wait correctly.
    let handle = sleep_cmd.pipe(&sleep_cmd).unchecked().start().unwrap();
    // Make sure try_wait doesn't block on it.
    assert!(handle.try_wait().unwrap().is_none());
    handle.kill().unwrap();
}

#[test]
fn test_input() {
    let expr = cmd!(path_to_exe("x_to_y")).stdin_bytes("xxx");
    let output = expr.read().unwrap();
    assert_eq!("yyy", output);
}

#[test]
fn test_stderr() {
    let (mut reader, writer) = ::os_pipe::pipe().unwrap();
    sh("echo hi>&2").stderr_file(writer).run().unwrap();
    let mut s = String::new();
    reader.read_to_string(&mut s).unwrap();
    assert_eq!(s.trim(), "hi");
}

#[test]
fn test_null() {
    let expr = cmd!(path_to_exe("cat"))
        .stdin_null()
        .stdout_null()
        .stderr_null();
    let output = expr.read().unwrap();
    assert_eq!("", output);
}

#[test]
fn test_path() {
    let dir = TempDir::new("test_path").unwrap();
    let input_file = dir.path().join("input_file");
    let output_file = dir.path().join("output_file");
    File::create(&input_file)
        .unwrap()
        .write_all(b"xxx")
        .unwrap();
    let expr = cmd!(path_to_exe("x_to_y"))
        .stdin_path(&input_file)
        .stdout_path(&output_file);
    let output = expr.read().unwrap();
    assert_eq!("", output);
    let mut file_output = String::new();
    File::open(&output_file)
        .unwrap()
        .read_to_string(&mut file_output)
        .unwrap();
    assert_eq!("yyy", file_output);
}

#[test]
fn test_swapping() {
    let output = sh("echo hi")
        .stdout_to_stderr()
        .stderr_capture()
        .run()
        .unwrap();
    let stderr = str::from_utf8(&output.stderr).unwrap().trim();
    assert_eq!("hi", stderr);

    // Windows compatible. (Requires no space before the ">".)
    let output = sh("echo hi>&2").stderr_to_stdout().read().unwrap();
    assert_eq!("hi", output);
}

#[test]
fn test_file() {
    let dir = TempDir::new("test_file").unwrap();
    let file = dir.path().join("file");
    File::create(&file).unwrap().write_all(b"example").unwrap();
    let expr = cmd!(path_to_exe("cat")).stdin_file(File::open(&file).unwrap());
    let output = expr.read().unwrap();
    assert_eq!(output, "example");
}

#[test]
fn test_ergonomics() {
    let mystr = "owned string".to_owned();
    let mypathbuf = Path::new("a/b/c").to_owned();
    let myvec = vec![1, 2, 3];
    // These are nonsense expressions. We just want to make sure they compile.
    let _ = sh("true")
        .stdin_path(&*mystr)
        .stdin_bytes(&*myvec)
        .stdout_path(&*mypathbuf);
    let _ = sh("true")
        .stdin_path(mystr)
        .stdin_bytes(myvec)
        .stdout_path(mypathbuf);

    // Unfortunately, this one doesn't work with our Into<Vec<u8>> bound on input().
    // TODO: Is it worth having these impls for &Vec in other cases?
    // let _ = sh("true").stdin_path(&mystr).stdin_bytes(&myvec).stdout_path(&mypathbuf);
}

#[test]
fn test_capture_both() {
    // Windows compatible, no space before ">", and we trim newlines at the end to avoid
    // dealing with the different kinds.
    let output = sh("echo hi && echo lo>&2")
        .stdout_capture()
        .stderr_capture()
        .run()
        .unwrap();
    assert_eq!("hi", str::from_utf8(&output.stdout).unwrap().trim());
    assert_eq!("lo", str::from_utf8(&output.stderr).unwrap().trim());
}

#[test]
fn test_dir() {
    // This test checks the interaction of `dir` and relative exe paths.
    // Make sure that's actually what we're testing.
    let pwd_path = path_to_exe("pwd");
    assert!(pwd_path.is_relative());

    let pwd = cmd!(pwd_path);

    // First assert that ordinary commands happen in the parent's dir.
    let pwd_output = pwd.read().unwrap();
    let pwd_path = Path::new(&pwd_output);
    assert_eq!(pwd_path, env::current_dir().unwrap());

    // Now create a temp dir and make sure we can set dir to it. This
    // also tests the interaction of `dir` and relative exe paths.
    let dir = TempDir::new("duct_test").unwrap();
    let pwd_output = pwd.dir(dir.path()).read().unwrap();
    let pwd_path = Path::new(&pwd_output);
    // pwd_path isn't totally canonical on Windows, because it
    // doesn't have a prefix. Thus we have to canonicalize both
    // sides. (This also handles symlinks in TMP_DIR.)
    assert_eq!(
        pwd_path.canonicalize().unwrap(),
        dir.path().canonicalize().unwrap()
    );
}

#[test]
fn test_env() {
    let output = cmd!(path_to_exe("print_env"), "foo")
        .env("foo", "bar")
        .read()
        .unwrap();
    assert_eq!("bar", output);
}

#[test]
fn test_full_env() {
    // Note that it's important that no other tests use this variable name,
    // because the test runner is multithreaded.
    let var_name = "TEST_FULL_ENV";

    // Capture the parent env, and make sure it does *not* contain our variable.
    let clean_env: HashMap<String, String> = env::vars().collect();
    assert!(
        !clean_env.contains_key(var_name),
        "why is this variable set?"
    );

    // Run a child process with that map passed to full_env(). It should be guaranteed not to
    // see our variable, regardless of any outer env() calls or changes in the parent.
    let clean_child = cmd!(path_to_exe("print_env"), var_name).full_env(clean_env);

    // Dirty the parent env. Should be suppressed.
    env::set_var(var_name, "junk1");
    // And make an outer env() call. Should also be suppressed.
    let dirty_child = clean_child.env(var_name, "junk2");

    // Check that neither of those have any effect.
    let output = dirty_child.read().unwrap();
    assert_eq!("", output);
}

#[test]
fn test_env_remove() {
    // Set an environment variable in the parent. Note that it's important that
    // no other tests use this variable name, because the test runner is
    // multithreaded.
    let var_name = "TEST_ENV_REMOVE";
    env::set_var(var_name, "junk2");

    // Run a command that observes the variable.
    let output1 = cmd!(path_to_exe("print_env"), var_name).read().unwrap();
    assert_eq!("junk2", output1);

    // Run the same command with that variable removed.
    let output2 = cmd!(path_to_exe("print_env"), var_name)
        .env_remove(var_name)
        .read()
        .unwrap();
    assert_eq!("", output2);
}

#[test]
fn test_env_remove_case_sensitivity() {
    // Env var deletion is particularly sensitive to the differences in
    // case-sensitivity between Unix and Windows. The semantics of env_remove
    // in duct must *match the platform*.

    // Set an environment variable in the parent. Note that it's important that
    // no other tests use this variable name, because the test runner is
    // multithreaded.
    let var_name = "TEST_ENV_REMOVE_CASE_SENSITIVITY";
    env::set_var(var_name, "abc123");

    // Run a command that tries to clear the same variable, but in lowercase.
    let output1 = cmd!(path_to_exe("print_env"), var_name)
        .env_remove(var_name.to_lowercase())
        .read()
        .unwrap();

    // Now try to clear that variable from the parent environment, again using
    // lowercase, and run the same command without `env_remove`.
    env::remove_var(var_name.to_lowercase());
    let output2 = cmd!(path_to_exe("print_env"), var_name).read().unwrap();

    // On Unix, env vars are case sensitive, and we don't expect either removal
    // to have any effect. On Windows, they're insensitive, and we expect both
    // removals to work. The key thing is that both approaches to removal have
    // the *same effect*.
    assert_eq!(output1, output2, "failed to match platform behavior!!!");

    // Go ahead and assert the exact expected output, just in case. If these
    // assertions ever break, it might be this test's fault and not the code's.
    if cfg!(windows) {
        assert_eq!(output1, "");
    } else {
        assert_eq!(output1, "abc123");
    }
}

#[test]
fn test_broken_pipe() {
    // If the input writing thread fills up its pipe buffer, writing will block. If the process
    // on the other end of the pipe exits while writer is waiting, the write will return an
    // error. We need to swallow that error, rather than returning it.
    let myvec = vec![0; 1_000_000];
    true_cmd().stdin_bytes(myvec).run().unwrap();
}

#[test]
fn test_silly() {
    // A silly test, purely for coverage.
    crate::IoValue::Null.try_clone().unwrap();
}

#[test]
fn test_path_sanitization() {
    // We don't do any chdir'ing in this process, because the tests runner is multithreaded,
    // and we don't want to screw up anyone else's relative paths. Instead, we shell out to a
    // small test process that does that for us.
    cmd!(path_to_exe("exe_in_dir"), path_to_exe("status"), "0")
        .run()
        .unwrap();
}

#[test]
fn test_before_spawn_hook() {
    let (reader, mut writer) = os_pipe::pipe().unwrap();
    let expr = cmd!(path_to_exe("cat")).before_spawn(move |cmd| {
        let reader_clone = reader.try_clone()?;
        cmd.stdin(reader_clone);
        Ok(())
    });
    writer.write_all(b"foobar").unwrap();
    drop(writer);
    let output = expr.read().unwrap();
    assert_eq!("foobar", output);
}

#[test]
fn test_trailing_comma() {
    let output = cmd!(path_to_exe("echo"), "trailing",).read().unwrap();
    assert_eq!("trailing", output);
}

#[test]
fn test_no_argument() {
    let output = cmd!(path_to_exe("echo")).read().unwrap();
    assert_eq!("", output);
}

#[test]
fn test_dropping_reader() {
    // Use an explicit stderr pipe to test the ReaderHandle's drop behavior.
    let (mut stderr_reader, stderr_writer) = os_pipe::pipe().unwrap();
    let mut reader_handle = cmd!(path_to_exe("sleep"), "1000000")
        .stdout_file(stderr_writer)
        .reader()
        .unwrap();
    // A zero-length read doesn't block.
    let n = reader_handle.read(&mut []).unwrap();
    assert_eq!(n, 0);
    // Try-wait returns None.
    let output = reader_handle.try_wait().unwrap();
    assert!(output.is_none());
    // Now we drop the reader. This kills the child.
    drop(reader_handle);
    // Now that the child is killed, reading the stderr pipe will not block.
    // (Note that our copy was closed when the temporary Expression above
    // dropped.)
    let mut stderr = Vec::new();
    let n = stderr_reader.read_to_end(&mut stderr).unwrap();
    assert_eq!(n, 0);
}

#[test]
fn test_kill_with_grandchild() -> io::Result<()> {
    // We're going to start a child process, and that child is going to start a
    // grandchild. The grandchild is going to sleep forever (1 day). We'll read
    // some output from the child to make sure it's done starting the
    // grandchild, and then we'll kill the child. Now, the grandchild will not
    // be killed, and it will still hold a write handle to the stdout pipe. So
    // this tests that the wait done by kill only waits on the child to exit,
    // and does not wait on IO to finish.
    //
    // This test leaks the grandchild process. I'm sorry.

    // Capturing stderr means an IO thread is spawned, even though we're using
    // a ReaderHandle to read stdout. What we're testing here is that kill()
    // doesn't wait on that IO thread.
    let mut reader = cmd!(path_to_exe("child_grandchild"))
        .stderr_capture()
        .reader()?;

    // Read "started" from the child to make sure we don't kill it before it
    // starts the grandchild.
    let mut started_read = [0; 7];
    reader.read_exact(&mut started_read)?;
    assert_eq!(&started_read, b"started");

    // Ok, this had better not block!
    reader.kill()
}

#[test]
fn test_debug_format() {
    let e = cmd!("foo", "bar", "baz").pipe(cmd!("bing", "bong"));
    assert_eq!(
        format!("{:?}", e),
        r#"Pipe(Cmd(["foo", "bar", "baz"]), Cmd(["bing", "bong"]))"#,
    );
}

#[test]
fn test_reader_try_wait() -> io::Result<()> {
    // Create a ReaderHandle for a cat process. Give cat 1 MB of data to echo
    // back to us, so that it will block on its stdout pipe until we start
    // reading.
    let bytes = vec![42; 1_000_000];
    let mut cat_reader = cmd!(path_to_exe("cat"))
        .stdin_bytes(bytes.clone())
        .reader()?;
    assert!(cat_reader.try_wait()?.is_none());
    let mut output = Vec::new();
    cat_reader.read_to_end(&mut output)?;
    assert_eq!(output, bytes);
    let output = cat_reader.try_wait()?.expect("is some");
    assert!(output.status.success());
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    Ok(())
}

#[test]
fn test_pids() -> io::Result<()> {
    let handle = true_cmd().start()?;
    let pids = handle.pids();
    assert_eq!(pids.len(), 1);
    handle.wait()?;

    let reader = true_cmd().reader()?;
    let pids = reader.pids();
    assert_eq!(pids.len(), 1);
    std::io::copy(&mut &reader, &mut std::io::sink())?;

    let handle = true_cmd()
        .pipe(true_cmd().stdout_null().pipe(true_cmd()))
        .start()?;
    let pids = handle.pids();
    assert_eq!(pids.len(), 3);
    handle.wait()?;

    let reader = true_cmd()
        .pipe(true_cmd().stdout_null().pipe(true_cmd()))
        .reader()?;
    let pids = reader.pids();
    assert_eq!(pids.len(), 3);
    std::io::copy(&mut &reader, &mut std::io::sink())?;

    Ok(())
}
