use sp_runtime::Fixed64;

/// Multiply a rational with an unsigned integer.
///
/// Example:
/// `assert_eq!(saturated_mul(Fixed64::from_rational(15, 10), 100), 150);`
pub(crate) fn saturated_mul(r: Fixed64, n: u64) -> u64 {
	// TODO: find some other way to avoid saturation when it is not necessary
	// tracking issue: https://github.com/paritytech/substrate/issues/5114
	r.saturated_multiply_accumulate(n).saturating_sub(n)
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn saturated_mul_test() {
		assert_eq!(saturated_mul(Fixed64::from_rational(15, 10), 100), 150);
	}

	// TODO: find some other way to avoid saturation when it is not necessary
	#[test]
	fn saturated_mul_saturation() {
		assert_eq!(saturated_mul(Fixed64::from_rational(15, 10), u64::max_value()), 0);
	}
}
