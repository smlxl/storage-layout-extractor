//! This module contains the type definitions necessary to support the
//! monitoring functionality for the extractor.
//!
//! # Best-Effort Monitoring
//!
//! Note that the monitoring provided by the watchdog is a best-effort approach.
//! It is not guaranteed that the watchdog is able to stop any given extractor
//! run in synchronous execution on a thread.
//!
//! If it is necessary to guarantee that the extractor can be stopped at any
//! point in the pipeline, future evolution might consider making the extractor
//! operate asynchronously. That way, workers can then be interrupted on a timer
//! naturally, rather than requiring cooperation from the extractor itself.

use std::{
    fmt::Debug,
    rc::Rc,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

use crate::constant::DEFAULT_WATCHDOG_POLL_LOOP_ITERATIONS;

/// A dynamically dispatched [`Watchdog`] instance.
pub type DynWatchdog = Rc<dyn Watchdog>;

/// The interface to an object that can be polled to see if the extractor needs
/// to abort processing.
///
/// The interface is simple, but it can encapsulate arbitrary logic as far as
/// the extractor is concerned, allowing the client to implement complex stop
/// logic.
pub trait Watchdog
where
    Self: Debug,
{
    /// Checks if the extractor should halt its analysis and return an error.
    #[must_use]
    fn should_stop(&self) -> bool;

    /// Gets the number of loop iterations the extractor should wait before
    /// polling the watchdog.
    #[must_use]
    fn poll_every(&self) -> usize;
}

/// An implementation of the [`Watchdog`] trait that does not place any
/// restrictions on the execution of the extractor.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct LazyWatchdog;

impl LazyWatchdog {
    /// Wraps `self` into an [`Rc`].
    #[must_use]
    pub fn in_rc(self) -> Rc<dyn Watchdog> {
        Rc::new(self)
    }
}

impl Watchdog for LazyWatchdog {
    fn should_stop(&self) -> bool {
        false
    }

    fn poll_every(&self) -> usize {
        // Something ridiculously huge so it basically never gets checked.
        1_000_000_000_000
    }
}

/// A watchdog that tells the extractor when to stop based on a flag in the form
/// of an atomic boolean.
///
/// By default, it requests that the extractor poll for watchdog status every
/// [`DEFAULT_WATCHDOG_POLL_LOOP_ITERATIONS`]. This is configurable by calling
/// [`Self::polling_every`].
#[derive(Clone, Debug)]
pub struct FlagWatchdog {
    /// The flag that should be mutated externally to stop the extractor by this
    /// watchdog.
    flag: Arc<AtomicBool>,

    /// The number of loop iterations the extractor should wait before polling
    /// the watchdog.
    poll_loop_iterations: usize,
}

impl FlagWatchdog {
    /// Constructs a new `FlagWatchdog` wrapping the provided `flag`.
    #[must_use]
    pub fn new(flag: Arc<AtomicBool>) -> Self {
        let poll_loop_iterations = DEFAULT_WATCHDOG_POLL_LOOP_ITERATIONS;
        Self {
            flag,
            poll_loop_iterations,
        }
    }

    /// Specifies the number of loop iterations that the extractor should wait
    /// before polling the watchdog for status.
    #[must_use]
    pub fn polling_every(mut self, iterations: usize) -> Self {
        self.poll_loop_iterations = iterations;
        self
    }

    /// Wraps the watchdog into an [`Rc`].
    #[must_use]
    pub fn in_rc(self) -> Rc<dyn Watchdog> {
        Rc::new(self)
    }
}

impl Watchdog for FlagWatchdog {
    fn should_stop(&self) -> bool {
        self.flag.load(Ordering::Relaxed)
    }

    fn poll_every(&self) -> usize {
        self.poll_loop_iterations
    }
}
