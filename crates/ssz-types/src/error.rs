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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_invalid_length() {
        let err = TypeError::InvalidLength {
            expected: 4,
            got: 7,
        };
        let msg = format!("{err}");
        assert_eq!(msg, "invalid length: expected 4, got 7");
    }

    #[test]
    fn display_over_capacity() {
        let err = TypeError::OverCapacity { max: 10, got: 15 };
        let msg = format!("{err}");
        assert_eq!(msg, "over capacity: max 10, got 15");
    }

    #[test]
    fn display_custom() {
        let err = TypeError::Custom("validator index out of range".into());
        let msg = format!("{err}");
        assert_eq!(msg, "validator index out of range");
    }

    #[test]
    fn error_trait_impl() {
        let err = TypeError::OverCapacity { max: 5, got: 6 };
        let err_ref: &dyn std::error::Error = &err;
        assert!(err_ref.to_string().contains("over capacity"));
    }
}
