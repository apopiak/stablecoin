use sp_runtime::Fixed64;

/// Multiply a rational with an unsigned integer.
///
/// Example:
/// `assert_eq!(saturated_mul(Fixed64::from_rational(15, 10), 100), 150);`
pub(crate) fn saturated_mul(r: Fixed64, uint: u64) -> u64 {
    r.saturated_multiply_accumulate(uint).saturating_sub(uint)
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
	fn saturated_mul_test() {
        assert_eq!(saturated_mul(Fixed64::from_rational(15, 10), 100), 150);
	}
}