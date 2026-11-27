//! The finish handshake (src/finish.rs: a caller waiting for its job's
//! last piece, and the workers finishing pieces) under Shuttle. This file
//! compiles the library's own finish.rs beside Shuttle's primitives, so
//! what is checked is the code the pool runs; a copy would drift. Run it so:
//!
//!     RUSTFLAGS="--cfg shuttle" cargo test --release --test shuttle_finish
//!
//! Without the cfg it compiles to nothing, so the ordinary suites are not
//! slowed by it. What it establishes: with two workers finishing one
//! piece each and a caller waiting for both, the caller returns on every
//! schedule Shuttle tries: no wake is lost between the caller's setting
//! its sleeping bit and its park, and a finisher that completes the count
//! while the bit is set unparks it. A schedule where every thread is
//! blocked is a deadlock Shuttle reports, which is the failure a lost
//! wake would be. (This test first ran under Loom, which does not model
//! SeqCst's total order; BLAKE3-Servil's handshakes are under one tool now,
//! Shuttle: Zooko, October 23.)
//!
//! Every schedule's operations are logged (`finish_sync`), and with
//! `FINISH_TRACE` set written to that file, a line a schedule:
//! tools/verify/tla/check.py checks each is a behavior of Finish.tla
//! (trace validation, FinishTrace.tla).
#![cfg(shuttle)]

/// Shuttle's primitives, under the name src/finish.rs imports them by,
/// each operation the file makes logged for trace validation
/// (tools/verify/tla/check.py checks every schedule's log against
/// Finish.tla). The log is the run's alone and costs the schedules
/// nothing Shuttle sees: it is no shared state of the model's threads.
mod finish_sync {
    pub use shuttle::sync::Mutex;
    pub use shuttle::sync::atomic::Ordering;

    std::thread_local! {
        /// This execution's operations: (thread, operation, atomic, value).
        pub static LOG: core::cell::RefCell<Vec<String>> = const { core::cell::RefCell::new(Vec::new()) };
        /// Atomics made so far this execution: Finish::new makes
        /// `published`, then `state`.
        pub static MADE: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
    }

    pub fn log(op: &str, atomic: usize, value: usize) {
        let id = format!("{:?}", shuttle::thread::current().id());
        LOG.with(|l| l.borrow_mut().push(format!("{id} {op} {atomic} {value}")));
    }

    /// Each operation is one `fetch_update`, logged from inside it: Shuttle
    /// switches threads before and after an atomic operation, never within
    /// one, so the log's order is the operations' (a log written before or
    /// after the operation could fall on the other side of a switch). The
    /// switches are the plain operations', so the schedules are too.
    pub struct AtomicUsize(shuttle::sync::atomic::AtomicUsize, usize);

    impl AtomicUsize {
        pub fn new(v: usize) -> Self {
            AtomicUsize(shuttle::sync::atomic::AtomicUsize::new(v), MADE.with(|m| m.replace(m.get() + 1)))
        }
        fn op(&self, name: &str, o: Ordering, f: impl Fn(usize) -> Option<usize>) -> usize {
            let r = self.0.fetch_update(o, o, |x| {
                log(name, self.1, x);
                f(x)
            });
            r.unwrap_or_else(|x| x)
        }
        pub fn load(&self, o: Ordering) -> usize {
            self.op("load", o, |_| None)
        }
        pub fn store(&self, v: usize, o: Ordering) {
            self.op("store", o, |_| Some(v));
        }
        pub fn fetch_add(&self, n: usize, o: Ordering) -> usize {
            self.op("fetch_add", o, |x| Some(x.wrapping_add(n)))
        }
        pub fn fetch_or(&self, n: usize, o: Ordering) -> usize {
            self.op("fetch_or", o, |x| Some(x | n))
        }
        pub fn fetch_and(&self, n: usize, o: Ordering) -> usize {
            self.op("fetch_and", o, |x| Some(x & n))
        }
    }

    pub mod thread {
        #[derive(Clone)]
        pub struct Thread(shuttle::thread::Thread);
        impl Thread {
            /// Logged before: the token is made available with no switch
            /// before it (the switch comes after).
            pub fn unpark(&self) {
                super::log("unpark", 0, 0);
                self.0.unpark();
            }
        }
        pub fn current() -> Thread {
            Thread(shuttle::thread::current())
        }
        /// Logged as it returns, having taken the token: no switch between.
        pub fn park() {
            shuttle::thread::park();
            super::log("park", 0, 0);
        }
    }
}

/// The finished execution's log, one line of it, appended to the file
/// $FINISH_TRACE names (none: nothing written), and the log cleared.
fn write_trace(pieces: usize) {
    let lines = finish_sync::LOG.with(|l| core::mem::take(&mut *l.borrow_mut()));
    finish_sync::MADE.with(|m| m.set(0));
    if let Some(path) = std::env::var_os("FINISH_TRACE") {
        use std::io::Write;
        // One write a line, so tests appending at once do not interleave.
        let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
        f.write_all(format!("{pieces}|{}\n", lines.join(";")).as_bytes()).unwrap();
    }
}

#[path = "../src/finish.rs"]
#[allow(dead_code)]
mod finish;

use finish::Finish;
use shuttle::sync::Arc;
use shuttle::sync::atomic::{AtomicUsize, Ordering};
use shuttle::thread;

/// The caller publishes `pieces`, each worker finishes one, the caller
/// waits for all; with `poll` polls before it sleeps. (A spurious wake,
/// which the operating system may give and the model's park does not,
/// is src/finish.rs's own test's.)
fn run(pieces: usize, polls: usize) {
    shuttle::check_pct(
        move || {
            let finish = Arc::new(Finish::new());
            finish.published.store(pieces, Ordering::SeqCst);
            finish.own();
            // Each worker writes its output, then counts its piece; the
            // caller reads every output as soon as `wait` returns (Sam
            // Shackleton's control, October 24: a return before the
            // outputs are visible is the bug a weaker ordering allows).
            let outputs: Arc<Vec<AtomicUsize>> = Arc::new((0..pieces).map(|_| AtomicUsize::new(0)).collect());
            let workers: Vec<_> = (0..pieces)
                .map(|i| {
                    let (f, out) = (finish.clone(), outputs.clone());
                    thread::spawn(move || {
                        out[i].store(1, Ordering::Relaxed);
                        f.finished(1)
                    })
                })
                .collect();
            let mut left = polls;
            finish.wait(pieces, || {
                thread::yield_now();
                left = left.saturating_sub(1);
                left > 0
            });
            for (i, out) in outputs.iter().enumerate() {
                assert_eq!(out.load(Ordering::Relaxed), 1, "wait returned without worker {i}'s output published");
            }
            assert_eq!(finish.finished_count(), pieces);
            for w in workers {
                w.join().unwrap();
            }
            write_trace(pieces);
        },
        3000,
        3,
    );
}

#[test]
fn a_caller_sleeping_at_once_is_woken_by_the_last_piece() {
    run(2, 0);
}

#[test]
fn a_caller_polling_once_then_sleeping_is_woken() {
    run(2, 1);
}

#[test]
fn one_piece_one_worker() {
    run(1, 0);
}
