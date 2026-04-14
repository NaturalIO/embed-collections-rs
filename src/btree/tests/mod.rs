mod api;
mod delete;
mod inter;
mod inter_borrow;
mod inter_underflow;
mod iter;
mod leaf;
mod leaf_borrow;
mod leaf_delete;
mod split;

use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::ops::Deref;
use core::sync::atomic::{AtomicUsize, Ordering::SeqCst};

/// Global alive counter for testing (new +1, drop -1)
static ALIVE_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Reset the alive counter to 0
fn reset_alive_count() {
    ALIVE_COUNT.store(0, SeqCst);
}

/// Get the current alive count (should be 0 at test end)
fn alive_count() -> usize {
    ALIVE_COUNT.load(SeqCst)
}

/// A test type that tracks alive count using a global static counter
/// new() +1, clone() +1, drop() -1, should be 0 at test end
struct CounterI32 {
    value: i32,
}

impl fmt::Display for CounterI32 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
impl fmt::Debug for CounterI32 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl CounterI32 {
    fn new(value: i32) -> Self {
        ALIVE_COUNT.fetch_add(1, SeqCst);
        Self { value }
    }
}

impl Clone for CounterI32 {
    fn clone(&self) -> Self {
        Self::new(self.value)
    }
}

impl From<i32> for CounterI32 {
    fn from(value: i32) -> Self {
        Self::new(value)
    }
}

impl PartialEq for CounterI32 {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl PartialEq<i32> for CounterI32 {
    fn eq(&self, other: &i32) -> bool {
        self.value == *other
    }
}

impl PartialEq<i32> for &CounterI32 {
    fn eq(&self, other: &i32) -> bool {
        self.value == *other
    }
}

impl Eq for CounterI32 {}

impl PartialOrd for CounterI32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.value.cmp(&other.value))
    }
}

impl Ord for CounterI32 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.value.cmp(&other.value)
    }
}

impl Drop for CounterI32 {
    fn drop(&mut self) {
        ALIVE_COUNT.fetch_sub(1, SeqCst);
    }
}

impl Deref for CounterI32 {
    type Target = i32;
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl Borrow<i32> for CounterI32 {
    fn borrow(&self) -> &i32 {
        &self.value
    }
}
