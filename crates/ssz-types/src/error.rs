#[cfg(feature = "alloc")]
use alloc::string::String;

/// Error returned when constructing a bounded SSZ type fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    /// A `Vector` was given the wrong number of elements.
    InvalidLength { expected: usize, got: usize },
    /// A `List` or `Bitlist` exceeded its maximum capacity.
    OverCapacity { max: usize, got: usize },
    /// A custom error message for other construction failures.
    #[cfg(feature = "alloc")]
    Custom(String),
}

#[cfg(feature = "std")]
impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TypeError::InvalidLength { expected, got } => {
                write!(f, "invalid length: expected {expected}, got {got}")
            }
            TypeError::OverCapacity { max, got } => {
                write!(f, "over capacity: max {max}, got {got}")
            }
            TypeError::Custom(msg) => write!(f, "{msg}"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TypeError {}
