// SPDX-License-Identifier: CC0-1.0

//! Absolute Locktimes

use core::{cmp, fmt};

use bitcoin::absolute;

/// Maximum allowed absolute locktime value.
pub const MAX_ABSOLUTE_LOCKTIME: u32 = 0x7FFF_FFFF;

/// Minimum allowed absolute locktime value.
///
/// In Bitcoin 0 is an allowed value, but in Miniscript it is not, because we
/// (ab)use the locktime value as a boolean in our Script fragments, and avoiding
/// this would reduce efficiency.
pub const MIN_ABSOLUTE_LOCKTIME: u32 = 1;

/// Error parsing an absolute locktime.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AbsLockTimeError {
    value: u32,
}

impl fmt::Display for AbsLockTimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.value < MIN_ABSOLUTE_LOCKTIME {
            f.write_str("absolute locktimes in Miniscript have a minimum value of 1")
        } else {
            debug_assert!(self.value > MAX_ABSOLUTE_LOCKTIME);
            write!(
                f,
                "absolute locktimes in Miniscript have a maximum value of 0x{:08x}; got 0x{:08x}",
                MAX_ABSOLUTE_LOCKTIME, self.value
            )
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for AbsLockTimeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> { None }
}

/// An absolute locktime that implements `Ord`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsLockTime(absolute::LockTime);

impl AbsLockTime {
    /// Constructs an `AbsLockTime` from an nLockTime value or the argument to `CHEKCLOCKTIMEVERIFY`.
    pub fn from_consensus(n: u32) -> Result<Self, AbsLockTimeError> {
        if n >= MIN_ABSOLUTE_LOCKTIME && n <= MAX_ABSOLUTE_LOCKTIME {
            Ok(Self(absolute::LockTime::from_consensus(n)))
        } else {
            Err(AbsLockTimeError { value: n })
        }
    }

    /// Returns the inner `u32` value. This is the value used when creating this `LockTime`
    /// i.e., `n OP_CHECKLOCKTIMEVERIFY` or nLockTime.
    ///
    /// This calls through to `absolute::LockTime::to_consensus_u32()` and the same usage warnings
    /// apply.
    pub fn to_consensus_u32(self) -> u32 { self.0.to_consensus_u32() }

    /// Whether this is a height-based locktime.
    pub fn is_block_height(&self) -> bool { self.0.is_block_height() }

    /// Whether this is a time-based locktime.
    pub fn is_block_time(&self) -> bool { self.0.is_block_time() }
}

impl From<AbsLockTime> for absolute::LockTime {
    fn from(lock_time: AbsLockTime) -> Self { lock_time.0 }
}

impl cmp::PartialOrd for AbsLockTime {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl cmp::Ord for AbsLockTime {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let this = self.0.to_consensus_u32();
        let that = other.0.to_consensus_u32();
        this.cmp(&that)
    }
}

impl fmt::Display for AbsLockTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Display::fmt(&self.0, f) }
}
