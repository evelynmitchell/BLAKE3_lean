//! Shuttle model check of src/source.rs (`Source`), the queue a Pipeline
//! hands its actions to the pool through, compiled beside Shuttle's
//! atomics, threads and mutex:
//!
//!     RUSTFLAGS="--cfg shuttle" cargo test --release --test shuttle_source
//!
//! What is real: `Source` (publish_actions, take's read and
//! compare-and-swap, run_waiting_action, wake_for_waiting) and its
//! `Finish` (src/finish.rs, whose `published` it counts on). What stands in:
//! the pool. One worker takes and runs actions, and with none sets its
//! parked bit, looks again, and parks while the bit stays set; a wake clears
//! the bit (as tools/verify/tla/PipeQueue.tla abstracts Park.tla's
//! handshake, which shuttle_park.rs checks). The owner publishes a slot's
//! two tasks, a piece's action and a group's, then waits for them to run:
//! running waiting actions itself (as block_on does) or not, then
//! wake_for_waiting, then asleep until an action has run.
//!
//! Each schedule is logged (`trace`) and, with SOURCE_TRACE set, written to
//! that file, a line a schedule: tools/verify/tla/check.py checks each is a
//! behavior of PipeQueue.tla (PipeQueueTrace.tla).
#![cfg(shuttle)]
#![allow(dead_code)]

/// The log: each atomic operation src/source.rs and src/finish.rs make,
/// from inside Shuttle's own step, so the log's order is the operations';
/// and the scenario's own steps.
mod trace {
    static ON: std::sync::Mutex<Option<(&'static str, Vec<String>)>> = std::sync::Mutex::new(None);

    pub fn log(site: &str, op: &str, old: &str, new: &str) {
        if let Some((_, lines)) = ON.lock().unwrap().as_mut() {
            let id = format!("{:?}", shuttle::thread::current().id());
            lines.push(format!("{id}|{site}|{op}|{old}|{new}"));
        }
    }
    pub fn note(what: &str) {
        log("note", what, "", "");
    }
    pub fn start(name: &'static str) {
        *ON.lock().unwrap() = Some((name, Vec::new()));
    }
    pub fn write() {
        let Some((name, lines)) = ON.lock().unwrap().take() else { return };
        if let Some(path) = std::env::var_os("SOURCE_TRACE") {
            use std::io::Write;
            let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
            f.write_all(format!("{name}:{}\n", lines.join(";")).as_bytes()).unwrap();
        }
    }
}

/// Shuttle's atomics, each naming the line that made it, logged.
mod source_sync {
    pub use shuttle::sync::atomic::{Ordering, fence};

    macro_rules! logged {
        ($name:ident, $int:ty) => {
            pub struct $name {
                inner: shuttle::sync::atomic::$name,
                site: String,
            }
            impl $name {
                #[track_caller]
                pub fn new(v: $int) -> Self {
                    let at = core::panic::Location::caller();
                    let file = at.file().rsplit('/').next().unwrap_or("");
                    $name { inner: shuttle::sync::atomic::$name::new(v), site: format!("{file}:{}", at.line()) }
                }
                /// The name a log gives it.
                pub fn named(v: $int, site: &str) -> Self {
                    $name { inner: shuttle::sync::atomic::$name::new(v), site: site.into() }
                }
                fn op(&self, op: &str, f: impl Fn($int) -> Option<$int>) -> Result<$int, $int> {
                    let o = Ordering::SeqCst;
                    self.inner.fetch_update(o, o, |x| {
                        let new = f(x);
                        crate::trace::log(&self.site, op, &format!("{x:?}"), &new.map_or(String::new(), |n| format!("{n:?}")));
                        new
                    })
                }
                pub fn load(&self, _: Ordering) -> $int {
                    self.op("load", |_| None).unwrap_or_else(|x| x)
                }
                pub fn store(&self, v: $int, _: Ordering) {
                    let _ = self.op("store", |_| Some(v));
                }
                pub fn swap(&self, v: $int, _: Ordering) -> $int {
                    self.op("swap", |_| Some(v)).unwrap_or_else(|x| x)
                }
                pub fn compare_exchange(&self, current: $int, new: $int, _: Ordering, _: Ordering) -> Result<$int, $int> {
                    self.op("cas", |x| (x == current).then_some(new))
                }
                pub fn compare_exchange_weak(&self, current: $int, new: $int, a: Ordering, b: Ordering) -> Result<$int, $int> {
                    self.compare_exchange(current, new, a, b)
                }
            }
        };
    }
    logged!(AtomicBool, bool);
    logged!(AtomicU64, u64);
    logged!(AtomicUsize, usize);
    impl AtomicUsize {
        pub fn fetch_add(&self, v: usize, _: Ordering) -> usize {
            self.op("add", |x| Some(x.wrapping_add(v))).unwrap_or_else(|x| x)
        }
        pub fn fetch_sub(&self, v: usize, _: Ordering) -> usize {
            self.op("sub", |x| Some(x.wrapping_sub(v))).unwrap_or_else(|x| x)
        }
        pub fn fetch_or(&self, v: usize, _: Ordering) -> usize {
            self.op("or", |x| Some(x | v)).unwrap_or_else(|x| x)
        }
        pub fn fetch_and(&self, v: usize, _: Ordering) -> usize {
            self.op("and", |x| Some(x & v)).unwrap_or_else(|x| x)
        }
    }

    /// A pointer's operations are not logged: the slot's words are read
    /// and written between `claimed` and `published`, which are.
    pub struct AtomicPtr<T>(shuttle::sync::atomic::AtomicPtr<T>);
    impl<T> AtomicPtr<T> {
        pub fn new(p: *mut T) -> Self {
            AtomicPtr(shuttle::sync::atomic::AtomicPtr::new(p))
        }
        pub fn load(&self, o: Ordering) -> *mut T {
            self.0.load(o)
        }
        pub fn store(&self, p: *mut T, o: Ordering) {
            self.0.store(p, o)
        }
    }
}

/// As tests/shuttle_finish.rs has it: Finish's two counts, named for the log.
mod finish_sync {
    pub use shuttle::sync::Mutex;
    pub use shuttle::sync::atomic::Ordering;
    pub use shuttle::thread;

    std::thread_local! {
        static MADE: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
    }
    /// Finish::new makes `published`, then `state`.
    pub struct AtomicUsize(crate::source_sync::AtomicUsize);
    impl AtomicUsize {
        pub fn new(v: usize) -> Self {
            let k = MADE.with(|m| m.replace(m.get() + 1));
            AtomicUsize(crate::source_sync::AtomicUsize::named(v, if k % 2 == 0 { "published" } else { "state" }))
        }
        pub fn load(&self, o: Ordering) -> usize {
            self.0.load(o)
        }
        pub fn store(&self, v: usize, o: Ordering) {
            self.0.store(v, o)
        }
        pub fn fetch_add(&self, v: usize, o: Ordering) -> usize {
            self.0.fetch_add(v, o)
        }
        pub fn fetch_sub(&self, v: usize, o: Ordering) -> usize {
            self.0.fetch_sub(v, o)
        }
        pub fn fetch_or(&self, v: usize, o: Ordering) -> usize {
            self.0.fetch_or(v, o)
        }
        pub fn fetch_and(&self, v: usize, o: Ordering) -> usize {
            self.0.fetch_and(v, o)
        }
        pub fn swap(&self, v: usize, o: Ordering) -> usize {
            self.0.swap(v, o)
        }
        pub fn compare_exchange(&self, c: usize, n: usize, a: Ordering, b: Ordering) -> Result<usize, usize> {
            self.0.compare_exchange(c, n, a, b)
        }
    }
}

#[path = "../src/finish.rs"]
mod finish;

#[path = "../src/source.rs"]
mod source;

pub(crate) use blake3_servil_core::thread_support::Platform;

/// What src/source.rs takes from lanes.rs: the pool's stand-in.
mod lanes {
    pub(crate) struct Job<'a>(core::marker::PhantomData<&'a ()>);

    #[repr(align(128))]
    pub(crate) struct OwnLine<T>(pub(crate) T);
    impl<T> std::ops::Deref for OwnLine<T> {
        type Target = T;
        fn deref(&self) -> &T {
            &self.0
        }
    }
    pub(crate) fn now() -> std::time::Instant {
        static BASE: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
        *BASE.get_or_init(std::time::Instant::now)
    }
    pub(crate) fn pool_platform() -> crate::Platform {
        crate::Platform::detect()
    }

    pub(crate) mod sources {
        use crate::source::Source;
        pub(crate) const ACTION_SME2: u64 = 1 << 63;
        pub(crate) fn keeps_polling(_: std::time::Instant, _: &mut std::time::Instant) -> bool {
            false
        }
        pub(crate) fn threads() -> usize {
            2
        }
        /// The pool's wake after a publish: a parked worker where two or more wait.
        pub(crate) fn wake_after_publish(source: &Source) {
            if source.waiting() >= 2 {
                crate::pool::wake();
            }
        }
        pub(crate) fn wake_one_for_waiting() {
            crate::pool::wake();
        }
    }
}

/// The worker's parked bit (PipeQueue.tla's: a wake clears it) and the
/// runs so far.
mod pool {
    use shuttle::sync::{Condvar, Mutex};

    pub struct State {
        pub bit: bool,
        pub stop: bool,
        pub runs: usize,
    }
    shuttle::lazy_static! {
        pub static ref STATE: Mutex<State> = Mutex::new(State { bit: false, stop: false, runs: 0 });
        pub static ref CHANGED: Condvar = Condvar::new();
    }
    pub fn wake() {
        let mut s = STATE.lock().unwrap();
        if s.bit {
            s.bit = false;
            CHANGED.notify_all();
        }
    }
}

use shuttle::thread;
use source::{Item, Source};

/// An action: its run counted, the waiting owner told.
unsafe fn run(_: *const (), _: u64, _: Platform) {
    let mut s = pool::STATE.lock().unwrap();
    trace::note("ran");
    s.runs += 1;
    pool::CHANGED.notify_all();
}

fn work(source: &'static Source) {
    loop {
        match source.take() {
            Some(Item::Action { run, context, arg }) => {
                // Sound: `run` is the test's own, stored by publish_actions.
                let f: unsafe fn(*const (), u64, Platform) = unsafe { core::mem::transmute(run) };
                unsafe { f(context as *const (), arg, Platform::detect()) };
            }
            Some(_) => unreachable!("an action source carries actions"),
            None => {
                let mut s = pool::STATE.lock().unwrap();
                if s.stop {
                    return;
                }
                s.bit = true;
                trace::note("bit");
                drop(s);
                let waiting = source.waiting();
                let mut s = pool::STATE.lock().unwrap();
                if !s.bit {
                    trace::note("woke");
                } else if waiting > 0 {
                    s.bit = false;
                    trace::note("again");
                } else {
                    trace::note("park");
                    while s.bit && !s.stop {
                        s = pool::CHANGED.wait(s).unwrap();
                    }
                }
            }
        }
    }
}

/// The owner's dispatches and its wait for them, `block` as block_on (it
/// runs waiting actions itself) or not.
fn queue(block: bool) {
    blake3_servil_core::initialize();
    shuttle::check_random(
        move || {
            trace::start(if block { "block" } else { "sleep" });
            let source: &'static Source = Box::leak(Box::new(Source::with_actions(6)));
            let worker = thread::spawn(move || work(source));
            for (what, n) in [("tasks", 2), ("piece", 1), ("group", 1)] {
                trace::note(&format!("{what} {n}"));
                // Sound: `run` is safe to call once with any context.
                unsafe { source.publish_actions(run, core::ptr::null(), &vec![0u64; n], false) };
            }
            loop {
                let seen = {
                    // The count the wait began after, read under the note.
                    let s = pool::STATE.lock().unwrap();
                    if s.runs == 4 {
                        break;
                    }
                    trace::note("wait");
                    s.runs
                };
                if block {
                    while source.run_waiting_action() {}
                }
                // The model's sleep: wake_for_waiting, and its look at the
                // count, noted where the count is read (under the lock).
                let at_sleep = {
                    let s = pool::STATE.lock().unwrap();
                    trace::note("sleep");
                    s.runs
                };
                source.wake_for_waiting();
                if at_sleep > seen {
                    continue;
                }
                let mut s = pool::STATE.lock().unwrap();
                while s.runs == seen {
                    s = pool::CHANGED.wait(s).unwrap();
                }
                trace::note("woken");
            }
            trace::note("finish");
            {
                let mut s = pool::STATE.lock().unwrap();
                s.stop = true;
                pool::CHANGED.notify_all();
            }
            worker.join().unwrap();
            trace::write();
        },
        500,
    );
}

#[test]
fn a_source_runs_every_action_once_with_its_owner_waiting() {
    queue(false);
}

#[test]
fn a_source_runs_every_action_once_with_its_owner_running_them() {
    queue(true);
}
