//! Shuttle model check of `src/waker.rs` (`WakerSlot`): causal race-freedom
//! on `UnsafeCell<Option<Waker>>` and lost-wake freedom under concurrent
//! finishers and re-registrations.
//!
//!     RUSTFLAGS="--cfg shuttle" cargo test --release --test shuttle_waker
//!
//! Both tests' schedules are logged (`log`) and, with `WAKER_TRACE` set,
//! written to that file, a line a schedule, tagged with its test's caller
//! script: tools/verify/tla/check.py checks each is a behavior of
//! Waker.tla (trace validation, WakerTrace.tla).
#![cfg(shuttle)]

/// This execution's operations, for trace validation: the slot's state
/// word, the cell, and the test's `done` and `woken` flags. Each atomic
/// operation is logged from inside Shuttle's own step (a `fetch_update`):
/// Shuttle switches threads before and after an atomic operation, never
/// within one, so the log's order is the operations'.
mod log {
    std::thread_local! {
        static LOG: core::cell::RefCell<Vec<String>> = const { core::cell::RefCell::new(Vec::new()) };
    }

    pub fn log(what: &str, op: &str, value: String) {
        let id = format!("{:?}", shuttle::thread::current().id());
        LOG.with(|l| l.borrow_mut().push(format!("{id}|{what}|{op}|{value}")));
    }

    /// The finished execution's log, a line after its test's `script`
    /// (WakerScripts.tla's name), appended to $WAKER_TRACE's file in one
    /// write; the log cleared.
    pub fn write(script: &str) {
        let lines = LOG.with(|l| core::mem::take(&mut *l.borrow_mut()));
        if let Some(path) = std::env::var_os("WAKER_TRACE") {
            use std::io::Write;
            let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
            f.write_all(format!("{script}:{}\n", lines.join(";")).as_bytes()).unwrap();
        }
    }

    pub fn clear() {
        LOG.with(|l| l.borrow_mut().clear());
    }

    /// A logged flag (the test's `done` and `woken`).
    pub struct Flag(shuttle::sync::atomic::AtomicBool, &'static str);

    impl Flag {
        pub fn new(v: bool, name: &'static str) -> Self {
            Flag(shuttle::sync::atomic::AtomicBool::new(v), name)
        }
        fn op(&self, op: &str, f: impl Fn(bool) -> Option<bool>) -> bool {
            let o = shuttle::sync::atomic::Ordering::SeqCst;
            self.0
                .fetch_update(o, o, |x| {
                    log(self.1, op, format!("{x}"));
                    f(x)
                })
                .unwrap_or_else(|x| x)
        }
        pub fn load(&self) -> bool {
            self.op("load", |_| None)
        }
        pub fn swap(&self, v: bool) -> bool {
            self.op("swap", |_| Some(v))
        }
        pub fn store(&self, v: bool) {
            self.op("store", |_| Some(v));
        }
    }
}

mod waker_sync {
    pub use shuttle::sync::atomic::{AtomicBool, Ordering, fence};

    /// The slot's state word, its operations logged (`log`).
    pub struct AtomicUsize(shuttle::sync::atomic::AtomicUsize);

    impl AtomicUsize {
        pub fn new(v: usize) -> Self {
            AtomicUsize(shuttle::sync::atomic::AtomicUsize::new(v))
        }
        fn op(&self, o: Ordering, f: impl Fn(usize) -> Option<usize>, what: impl Fn(usize) -> String) -> Result<usize, usize> {
            self.0.fetch_update(o, o, |x| {
                crate::log::log("state", &what(x), String::new());
                f(x)
            })
        }
        pub fn load(&self, o: Ordering) -> usize {
            self.op(o, |_| None, |x| format!("load {x}")).unwrap_or_else(|x| x)
        }
        pub fn store(&self, v: usize, o: Ordering) {
            let _ = self.op(o, |_| Some(v), |x| format!("store {x} {v}"));
        }
        pub fn compare_exchange(&self, current: usize, new: usize, o: Ordering, _f: Ordering) -> Result<usize, usize> {
            self.op(o, |x| (x == current).then_some(new), |x| format!("cas {x} {current} {new}"))
        }
    }
    pub struct UnsafeCell<T> {
        busy: AtomicBool,
        inner: core::cell::UnsafeCell<T>,
    }
    impl<T> UnsafeCell<T> {
        pub fn new(v: T) -> Self {
            Self { busy: AtomicBool::new(false), inner: core::cell::UnsafeCell::new(v) }
        }
    }
    pub fn spin() {
        shuttle::thread::yield_now();
    }
    pub unsafe fn with_mut<T, R>(cell: &UnsafeCell<T>, f: impl FnOnce(&mut T) -> R) -> R {
        assert!(!cell.busy.swap(true, Ordering::SeqCst), "concurrent mutable access to WakerSlot::waker");
        shuttle::thread::yield_now();
        // Logged with no switch before `f`: the cell's use, one step.
        crate::log::log("cell", "use", String::new());
        let out = f(unsafe { &mut *cell.inner.get() });
        assert!(cell.busy.swap(false, Ordering::SeqCst));
        out
    }
}

#[path = "../src/waker.rs"]
mod waker;

use core::task::{Context, RawWaker, RawWakerVTable, Waker};
use shuttle::sync::Arc;
use shuttle::sync::atomic::{AtomicUsize, Ordering};
use shuttle::thread;
use waker::WakerSlot;

struct ParkWake {
    waiter: thread::Thread,
    woken: log::Flag,
}

unsafe fn clone_raw(ptr: *const ()) -> RawWaker {
    unsafe { Arc::increment_strong_count(ptr as *const ParkWake) };
    RawWaker::new(ptr, &VTABLE)
}
unsafe fn wake_raw(ptr: *const ()) {
    let arc = unsafe { Arc::from_raw(ptr as *const ParkWake) };
    arc.woken.store(true);
    arc.waiter.unpark();
}
unsafe fn wake_ref_raw(ptr: *const ()) {
    let p = unsafe { &*(ptr as *const ParkWake) };
    p.woken.store(true);
    p.waiter.unpark();
}
unsafe fn drop_raw(ptr: *const ()) {
    drop(unsafe { Arc::from_raw(ptr as *const ParkWake) });
}

static VTABLE: RawWakerVTable = RawWakerVTable::new(clone_raw, wake_raw, wake_ref_raw, drop_raw);

fn make_shuttle_waker(state: &Arc<ParkWake>) -> Waker {
    let raw = Arc::into_raw(Arc::clone(state)) as *const ();
    unsafe { Waker::from_raw(RawWaker::new(raw, &VTABLE)) }
}

#[test]
fn waker_slot_never_loses_a_wake_or_races_under_concurrent_finishers() {
    shuttle::check_pct(
        || {
            log::clear();
            let slot = Arc::new(WakerSlot::new());
            let payload = Arc::new(AtomicUsize::new(0));
            let done = Arc::new(log::Flag::new(false, "done"));

            let (s1, p1, d1) = (Arc::clone(&slot), Arc::clone(&payload), Arc::clone(&done));
            let worker = thread::spawn(move || {
                p1.store(42, Ordering::Relaxed);
                d1.swap(true);
                s1.notify_after_seqcst();
            });

            let s2 = Arc::clone(&slot);
            let other = thread::spawn(move || {
                s2.notify_after_seqcst();
            });

            let wake_state = Arc::new(ParkWake { waiter: thread::current(), woken: log::Flag::new(false, "woken") });
            let waker = make_shuttle_waker(&wake_state);
            let cx = Context::from_waker(&waker);

            loop {
                if done.load() {
                    break;
                }
                slot.register(&cx);
                if done.load() {
                    slot.clear();
                    break;
                }
                while !wake_state.woken.swap(false) {
                    thread::park();
                }
            }

            assert_eq!(payload.load(Ordering::Relaxed), 42);
            worker.join().unwrap();
            other.join().unwrap();
            log::write("OneWait");
        },
        3000,
        3,
    );
}

#[test]
fn overwrite_and_clear_drop_wakers_and_prevent_spurious_wakes() {
    shuttle::check_pct(
        || {
            log::clear();
            let slot = Arc::new(WakerSlot::new());
            let s_worker = Arc::clone(&slot);
            let worker = thread::spawn(move || {
                s_worker.notify_after_seqcst();
            });

            let w1_state = Arc::new(ParkWake { waiter: thread::current(), woken: log::Flag::new(false, "woken") });
            let w1 = make_shuttle_waker(&w1_state);
            slot.register(&Context::from_waker(&w1));

            let w2_state = Arc::new(ParkWake { waiter: thread::current(), woken: log::Flag::new(false, "woken") });
            let w2 = make_shuttle_waker(&w2_state);
            slot.register(&Context::from_waker(&w2));
            slot.clear();
            worker.join().unwrap();

            drop((w1, w2));
            assert_eq!(Arc::strong_count(&w1_state), 1, "first waker dropped");
            assert_eq!(Arc::strong_count(&w2_state), 1, "cleared waker dropped");
            log::write("Swap");
        },
        2000,
        3,
    );
}
