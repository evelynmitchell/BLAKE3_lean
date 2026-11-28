//! A source of the workers' work (lanes.rs, `sources`): a numbered sequence
//! of items that its owner publishes and workers claim. A Pipeline's
//! actions sit in a ring, publication `p` at `p % len`; a caller's one-shot
//! job is a run of pieces. One owner writes `published` (one Release
//! store); takers advance `claimed` by compare-and-swap, only below
//! `published`.
//!
//! Its own file, on its own primitives (`source_sync`), so that
//! tests/shuttle_source.rs compiles this same file beside Shuttle's: the
//! pool's registry, wakes and threads stay in lanes.rs.

use crate::Platform;
use crate::lanes::sources::{ACTION_SME2, keeps_polling, threads, wake_after_publish, wake_one_for_waiting};
use crate::lanes::{Job, OwnLine, now, pool_platform};
use crate::source_sync::{AtomicBool, AtomicPtr, AtomicU64, AtomicUsize, Ordering, fence};

/// A pipeline's item in a source: atomic fields read before the claimer's
/// CAS (`take`) and rewritten only after `claimed` has passed it
/// (`publish_actions`), so no claimer copies non-atomic memory after its
/// claim (BLAKE3 #302). Each slot carries its own `near` wake-preference
/// hint so mixed publications in one queue never overwrite earlier items'
/// wake policy.
struct Action {
    run: AtomicPtr<()>,
    context: AtomicPtr<()>,
    arg: AtomicU64,
    near: AtomicBool,
}

#[repr(align(128))]
pub(crate) struct Source {
    pub(crate) claimed: OwnLine<AtomicUsize>,
    /// A pipeline's actions (`with_actions`), publication `p`'s at
    /// `p % len`; empty for a caller's jobs.
    actions: Box<[Action]>,
    /// A caller's current job and its first number; the job stays the
    /// claimed numbers' until `finish.finished` passes them.
    job: AtomicPtr<Job<'static>>,
    base: AtomicUsize,
    /// Whether the current job stays with the workers of its caller's
    /// place (a job under FAR_LEN, where workers have places).
    pub(crate) near: AtomicBool,
    /// What is published and what is finished, and the handshake
    /// between the waiting caller and the worker finishing its last
    /// piece (crate::finish, which Loom checks).
    pub(crate) finish: crate::finish::Finish,
}

// Sound: every slot is written by one publisher after the previous claimer
// copied its fields out (across Release/Acquire on `published` / `claimed`);
// action words are atomics, `Finish::owner` is synchronized by its mutex,
// and the remaining fields are atomic.
unsafe impl Sync for Source {}
// Sound: `Source` holds only atomics, `Finish` (mutex-synchronized), and self-synchronized raw action slots.
unsafe impl Send for Source {}

/// What a claim takes: a stream's task, a pipeline's action, or a run
/// of a job's pieces (`n` from `index`, consecutive).
pub(crate) enum Item {
    Action { run: *mut (), context: *mut (), arg: u64 },
    Pieces(*const Job<'static>, usize, usize),
}

impl Source {
    /// A source for a calling thread's one-shot jobs.
    pub(crate) fn new() -> Source {
        Self::with_actions(0)
    }

    /// A source with `actions` slots for a pipeline's items.
    pub(crate) fn with_actions(actions: usize) -> Source {
        Source {
            claimed: OwnLine(AtomicUsize::new(0)),
            actions: (0..actions)
                .map(|_| Action {
                    run: AtomicPtr::new(core::ptr::null_mut()),
                    context: AtomicPtr::new(core::ptr::null_mut()),
                    arg: AtomicU64::new(0),
                    near: AtomicBool::new(false),
                })
                .collect(),
            job: AtomicPtr::new(core::ptr::null_mut()),
            base: AtomicUsize::new(0),
            near: AtomicBool::new(false),
            finish: crate::finish::Finish::new(),
        }
    }

    pub(crate) fn actions_len(&self) -> usize {
        self.actions.len()
    }

    pub(crate) fn carries_tasks(&self) -> bool {
        !self.actions.is_empty()
    }

    /// Publish one or more pipeline actions in order with one Release
    /// store and one fence, then wake parked workers only where awake
    /// workers fall short of the items waiting.
    ///
    /// # Safety
    ///
    /// This source must be an action source with a single publisher at a
    /// time, and every `(run, context, arg)` tuple published must be safe
    /// for a worker (or caller) to invoke once with the assigned `Platform`.
    pub(crate) unsafe fn publish_actions(&self, run: unsafe fn(*const (), u64, Platform), context: *const (), args: &[u64], near: bool) {
        debug_assert!(!args.is_empty());
        let p = self.finish.published.load(Ordering::Relaxed);
        let next = p.checked_add(args.len()).expect("Source action ticket counter exhausted");
        assert!(p - self.claimed.load(Ordering::Acquire) + args.len() <= self.actions.len(), "a source's actions hold every item not yet taken");
        let cap = self.actions.len();
        for (k, &arg) in args.iter().enumerate() {
            let slot = &self.actions[(p + k) % cap];
            slot.run.store(run as *mut (), Ordering::Relaxed);
            slot.context.store(context as *mut (), Ordering::Relaxed);
            slot.arg.store(arg, Ordering::Relaxed);
            slot.near.store(near, Ordering::Relaxed);
        }
        self.finish.published.store(next, Ordering::Release);
        fence(Ordering::SeqCst);
        wake_after_publish(self);
    }

    /// Whether the action currently at the head of this source's waiting
    /// ring prefers local-cache speculative wakes.
    pub(crate) fn front_action_near(&self) -> bool {
        let c = self.claimed.load(Ordering::Acquire);
        let p = self.finish.published.load(Ordering::Acquire);
        c < p && self.actions[c % self.actions.len()].near.load(Ordering::Relaxed)
    }

    /// Run one unclaimed action from this source on the calling thread,
    /// if any remains.
    pub(crate) fn run_waiting_action(&self) -> bool {
        match self.take() {
            Some(Item::Action { run, context, arg }) => {
                // Sound: `publish_actions` stored an `unsafe fn(*const (), u64, Platform)` function pointer and live `context` valid until completion.
                let f: unsafe fn(*const (), u64, Platform) = unsafe { core::mem::transmute(run) };
                unsafe { f(context as *const (), arg & !ACTION_SME2, pool_platform()) };
                true
            }
            Some(_) => unreachable!("an action source carries actions"),
            None => false,
        }
    }

    #[cfg(test)]
    pub(super) fn own_for_test(&self) {
        self.finish.own();
    }

    /// Make `job` the caller's current job, its pieces `0..own` the
    /// caller's own: the number `finished` must reach when it is done.
    ///
    /// # Safety
    ///
    /// This source must be a single-publisher job source, `own <= pieces`,
    /// and `job` (along with all buffers its pieces read/write) must stay
    /// valid until `self.wait(target)` returns.
    pub(crate) unsafe fn publish_job(&self, job: *mut Job<'static>, pieces: usize, own: usize, near: bool) -> usize {
        let base = self.finish.published.load(Ordering::Relaxed);
        debug_assert_eq!(self.finish.finished_count(), base, "the last job is finished");
        let target = base.checked_add(pieces).expect("Source job counter overflow");
        assert!(target < crate::finish::SLEEPING, "Source job counter reached Finish::SLEEPING limit");
        self.near.store(near, Ordering::Relaxed);
        self.job.store(job, Ordering::Relaxed);
        self.base.store(base, Ordering::Relaxed);
        // No worker can claim a number yet (claimed == published), so
        // this store alone moves `claimed` past the caller's own pieces.
        self.claimed.store(base + own, Ordering::Relaxed);
        self.finish.published.store(target, Ordering::Release);
        fence(Ordering::SeqCst);
        target
    }

    /// Claim the next published item, if any.
    pub(crate) fn take(&self) -> Option<Item> {
        let mut c = self.claimed.load(Ordering::Acquire);
        loop {
            let p = self.finish.published.load(Ordering::Acquire);
            if c >= p {
                return None;
            }
            if !self.actions.is_empty() {
                let slot = &self.actions[c % self.actions.len()];
                let run = slot.run.load(Ordering::Relaxed);
                let context = slot.context.load(Ordering::Relaxed);
                let arg = slot.arg.load(Ordering::Relaxed);
                match self.claimed.compare_exchange_weak(c, c + 1, Ordering::AcqRel, Ordering::Acquire) {
                    Ok(_) => return Some(Item::Action { run, context, arg }),
                    Err(now) => {
                        c = now;
                        continue;
                    }
                }
            }
            let n = Self::run_len(p - c, threads());
            match self.claimed.compare_exchange_weak(c, c + n, Ordering::AcqRel, Ordering::Acquire) {
                Ok(_) => return Some(Item::Pieces(self.job.load(Ordering::Relaxed), c - self.base.load(Ordering::Relaxed), n)),
                Err(now) => c = now,
            }
        }
    }

    /// Get the number of pieces one claim takes of `waiting` pieces of a
    /// job shared by `threads` threads: a 2 * threads-th of what waits,
    /// one at least, so runs shrink toward the end (guided
    /// self-scheduling).
    fn run_len(waiting: usize, threads: usize) -> usize {
        (waiting / (2 * threads)).max(1)
    }

    #[cfg(test)]
    pub(crate) fn run_len_for_tests(waiting: usize, threads: usize) -> usize {
        Self::run_len(waiting, threads)
    }

    pub(crate) fn waiting(&self) -> usize {
        self.finish.published.load(Ordering::Acquire).saturating_sub(self.claimed.load(Ordering::Acquire))
    }

    /// Wake a parked worker for a task this stream has published that no
    /// thread has taken: `publish` wakes one for the second task in
    /// waiting, expecting the caller to take a lone one, and a caller
    /// that only collects never does (it waited forever, the workers
    /// asleep: the C API's stream test on an i7-12700K and on GitHub's
    /// 4-CPU runners; Devon Jonte, #99). Always calls `wake_one()` (which
    /// tries the caller's place first and still wakes a remote parked
    /// worker if local workers are busy) so sleeping external executors
    /// always make progress.
    pub(crate) fn wake_for_waiting(&self) {
        if self.waiting() > 0 {
            wake_one_for_waiting();
        }
    }

    /// Count `n` of the caller's job's pieces finished (their outputs
    /// written before); the last one wakes a caller parked for it.
    pub(crate) fn finished(&self, n: usize) {
        self.finish.finished(n);
    }

    /// Wait until `finished` reaches `target`: polling for
    /// SPIN_BEFORE_SLEEP, then parked until the worker finishing the
    /// last piece unparks this thread.
    pub(crate) fn wait(&self, target: usize) {
        let started = now();
        let mut yielded = started;
        self.finish.wait(target, || keeps_polling(started, &mut yielded));
    }
}
