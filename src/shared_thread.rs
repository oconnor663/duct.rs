use std::sync::{Condvar, Mutex, OnceLock};
use std::thread;

/// A wrapper around std::thread::JoinHandle that allows for multiple joiners. Most methods take
/// `&self` and implicitly propagate panics from the shared thread.
#[derive(Debug)]
pub struct SharedThread<T> {
    thread: Mutex<Option<thread::JoinHandle<T>>>,
    condvar: Condvar,
    result: OnceLock<T>,
}

impl<T: Send + 'static> SharedThread<T> {
    pub fn spawn<F>(f: F) -> Self
    where
        F: FnOnce() -> T + Send + 'static,
    {
        Self::new(thread::spawn(f))
    }
}

// A thread that sticks its result in a lazy cell, so that multiple callers can see it.
impl<T> SharedThread<T> {
    pub fn new(handle: thread::JoinHandle<T>) -> Self {
        SharedThread {
            thread: Mutex::new(Some(handle)),
            condvar: Condvar::new(),
            result: OnceLock::new(),
        }
    }

    pub fn try_join(&self) -> Option<&T> {
        let mut guard = self.thread.lock().unwrap();
        if let Some(thread) = guard.take() {
            if thread.is_finished() {
                // Joining will not block in this case, and we can do it while holding the Mutex.
                let result = thread.join();
                // It's not possible for a .join() thread to be waiting on the Condvar at this
                // point, because that thread would have .take()n the thread handle.
                debug_assert!(self.result.get().is_none());
                _ = self.result.set(result.expect("shared thread panicked"));
            } else {
                // The thread is likely to block if we join it. Put it back.
                *guard = Some(thread);
            }
        }
        self.result.get()
    }

    pub fn join(&self) -> &T {
        let mut guard = self.thread.lock().unwrap();
        if let Some(thread) = guard.take() {
            // It's our job to block on join(). Release the mutex while we block, so that we don't
            // interfere with calls to Self::try_join in the meantime.
            drop(guard);
            let result = thread.join();
            // Retake the mutex so that notify_all() and wait() don't race.
            guard = self.thread.lock().unwrap();
            self.condvar.notify_all();
            debug_assert!(self.result.get().is_none());
            _ = self.result.set(result.expect("shared thread panicked"));
            drop(guard);
            return self.result.get().unwrap();
        }
        // Either another thread has already joined, in which case the result will be populated, or
        // another thread is in the process of joining, in which case we'll wait for them to notify
        // the Condvar.
        loop {
            match self.result.get() {
                Some(result) => return result,
                None => {
                    guard = self.condvar.wait(guard).unwrap();
                }
            }
        }
    }

    pub fn into_result(self) -> T {
        self.join();
        self.result.into_inner().unwrap()
    }
}

impl<T> From<thread::JoinHandle<T>> for SharedThread<T> {
    fn from(handle: thread::JoinHandle<T>) -> Self {
        Self::new(handle)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::sync::atomic::{AtomicBool, Ordering::Relaxed};

    #[test]
    fn test_join_and_try_join() {
        static STOP_FLAG: AtomicBool = AtomicBool::new(false);
        let bg_thread = SharedThread::spawn(|| {
            while !STOP_FLAG.load(Relaxed) {}
            42
        });
        // Spawn 10 joiner threads that all simultaneously try to join the backgroud thread.
        thread::scope(|scope| {
            let mut joiner_handles = Vec::new();
            for _ in 0..10 {
                joiner_handles.push(scope.spawn(|| {
                    bg_thread.join();
                }));
            }
            // try_join will always return None here.
            for _ in 0..100 {
                assert!(bg_thread.try_join().is_none());
            }
            STOP_FLAG.store(true, Relaxed);
            // One of the joiner threads almost certainly has the underlying thread handle, and
            // eventually it'll set SharedThread::result and one of these try_joins will return Some.
            while bg_thread.try_join().is_none() {}
            assert_eq!(bg_thread.try_join(), Some(&42));
        });
    }

    #[test]
    fn test_try_join_only() {
        static STOP_FLAG: AtomicBool = AtomicBool::new(false);
        let bg_thread = SharedThread::spawn(|| {
            while !STOP_FLAG.load(Relaxed) {}
            42
        });
        // try_join will always return None here.
        for _ in 0..100 {
            assert!(bg_thread.try_join().is_none());
        }
        STOP_FLAG.store(true, Relaxed);
        // Eventually one of these try_join's will see .is_finished() = true and join the thread.
        while bg_thread.try_join().is_none() {}
        assert_eq!(bg_thread.try_join(), Some(&42));
    }

    #[test]
    fn test_from_and_into_inner() {
        let thread = thread::spawn(|| String::from("foo"));
        let shared: SharedThread<String> = thread.into();
        let result: String = shared.into_result();
        assert_eq!(result, "foo");
    }
}
