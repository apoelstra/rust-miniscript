// SPDX-License-Identifier: CC0-1.0

//! Relative Locktimes

use core::{cmp, convert, fmt};

use bitcoin::{relative, Sequence};

/// Error parsing an absolute locktime.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RelLockTimeError {
    value: u32,
}

impl fmt::Display for RelLockTimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.value == 0 {
            f.write_str("relative locktimes in Miniscript have a minimum value of 1")
        } else {
            debug_assert!(Sequence::from_consensus(self.value)
                .to_relative_lock_time()
                .is_none());
            write!(f, "locktime value {} is not a valid BIP68 relative locktime", self.value)
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for RelLockTimeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> { None }
}

/// A relative locktime which implements `Ord`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelLockTime(Sequence);

impl RelLockTime {
    /// The "0 blocks" constant.
    pub const ZERO: Self = RelLockTime(Sequence::ZERO);

    /// Constructs an `RelLockTime` from an nLockTime value or the argument to `CHEKCLOCKTIMEVERIFY`.
    pub fn from_consensus(n: u32) -> Result<Self, RelLockTimeError> {
        convert::TryFrom::try_from(Sequence::from_consensus(n))
    }

    /// Returns the inner `u32` value. This is the value used when creating this `LockTime`
    /// i.e., `n OP_CHECKSEQUENCEVERIFY` or `nSequence`.
    pub fn to_consensus_u32(self) -> u32 { self.0.to_consensus_u32() }

    /// Takes a 16-bit number of blocks and produces a relative locktime from it.
    pub fn from_height(height: u16) -> Self { RelLockTime(Sequence::from_height(height)) }

    /// Takes a 16-bit number of 512-second time intervals and produces a relative locktime from it.
    pub fn from_512_second_intervals(time: u16) -> Self {
        RelLockTime(Sequence::from_512_second_intervals(time))
    }

    /// Whether this timelock is blockheight-based.
    pub fn is_height_locked(&self) -> bool { self.0.is_height_locked() }

    /// Whether this timelock is time-based.
    pub fn is_time_locked(&self) -> bool { self.0.is_time_locked() }
}

impl convert::TryFrom<Sequence> for RelLockTime {
    type Error = RelLockTimeError;
    fn try_from(seq: Sequence) -> Result<Self, RelLockTimeError> {
        if seq.is_relative_lock_time() && seq != Sequence::ZERO {
            Ok(RelLockTime(seq))
        } else {
            Err(RelLockTimeError { value: seq.to_consensus_u32() })
        }
    }
}

impl From<RelLockTime> for Sequence {
    fn from(lock_time: RelLockTime) -> Sequence { lock_time.0 }
}

impl From<RelLockTime> for relative::LockTime {
    fn from(lock_time: RelLockTime) -> relative::LockTime {
        lock_time.0.to_relative_lock_time().unwrap()
    }
}

impl cmp::PartialOrd for RelLockTime {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl cmp::Ord for RelLockTime {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let this = self.0.to_consensus_u32();
        let that = other.0.to_consensus_u32();
        this.cmp(&that)
    }
}

impl fmt::Display for RelLockTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Display::fmt(&self.0, f) }
}
