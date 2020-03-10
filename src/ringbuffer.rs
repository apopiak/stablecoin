use core::marker::PhantomData;
use codec::{Codec, Encode, Decode, EncodeLike};
use frame_support::storage::{StorageValue, StorageMap};

pub type Index = u16;

pub struct RingBufferTransient<T, I, B, M> 
where T: ?Sized
{
	start: Index,
	end: Index,
	_t: PhantomData<(I, B, M, T)>,
}

impl<T, I, B, M> RingBufferTransient<T, I, B, M>
where
	I: Codec + EncodeLike,
 	B: StorageValue<(Index, Index), Query = (Index, Index)>,
 	M: StorageMap<Index, I, Query = I>,
	T: RingBufferTrait<I, Item = I, Bounds = B, Map = M> + ?Sized
{

	pub fn new() -> RingBufferTransient<T, I, B, M> {
		let (start, end) = <<T as RingBufferTrait<I>>::Bounds>::get();
		RingBufferTransient { start, end, _t: PhantomData }
	}
}

pub trait RingBufferTrait<I>
where
	I: Codec + EncodeLike,
{
	type Item: Codec;
	type Bounds: StorageValue<(Index, Index)>;
	type Map: StorageMap<Index, I>;

	fn commit(&self);

	fn push(&mut self, i: Self::Item);
	fn push_front(&mut self, i: Self::Item);

	fn pop(&mut self) -> Option<Self::Item>;
}

impl<T, I, B, M> RingBufferTrait<I> for RingBufferTransient<T, I, B, M>
where
	I: Codec + EncodeLike,
	B: StorageValue<(Index, Index), Query = (Index, Index)>,
	M: StorageMap<Index, I, Query = I>,
	T: RingBufferTrait<I>,
{
	type Item = I;
	type Bounds = B;
	type Map = M;

	fn commit(&self) {
		Self::Bounds::put((self.start, self.end));
	}

	/// Push a bond into the queue to be payed out at a later date.
	///
	/// Returns the new end index of the bonds queue.
	fn push(&mut self, item: Self::Item) {
		Self::Map::insert(self.end, item);
		// this will intentionally overflow and wrap around when bonds_end
		// reaches `Index::max_value` because we want a ringbuffer.
		let next_index = self.end.wrapping_add(1);
		if next_index == self.start {
			// overwrite the oldest item in the FIFO ringbuffer
			self.start = self.start.wrapping_add(1);
			self.end = next_index;
		} else {
			self.end = next_index;
		}
	}

	fn push_front(&mut self, item: Self::Item) {
		if self.start == self.end {
			<Self as RingBufferTrait<I>>::push(self, item);
			return;
		}
		let index = self.start.wrapping_sub(1);
		Self::Map::insert(index, item);
		self.start = index;
	}

	fn pop(&mut self) -> Option<Self::Item> {
		if self.start == self.end {
			return None;
		}
		let item = Self::Map::take(self.start);
		self.start = self.start.wrapping_add(1);
		
		item.into()
	}
}

/// tests for this pallet
#[cfg(test)]
mod tests {
	use super::*;
	use RingBufferTrait;
	use itertools::Itertools;
	use log;
	use more_asserts::*;
	use quickcheck::{QuickCheck, TestResult};
	use rand::{thread_rng, Rng};
	use std::sync::atomic::{AtomicU64, Ordering};

	use frame_support::{assert_ok, decl_module, decl_storage, impl_outer_origin, parameter_types, weights::Weight};
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup},
		Perbill,
	};
	use system;

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	// For testing the pallet, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;

	pub trait Trait: system::Trait {}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		}
	}

	#[derive(Clone, PartialEq, Encode, Decode, Default)]
	struct SomeStruct {
		foo: u16,
		bar: u32,
	}

	decl_storage! {
		trait Store for Module<T: Trait> as RingBufferTest {
			TestMap get(fn get_test_value): map hasher(twox_64_concat) Index => SomeStruct;
			TestRange get(fn get_test_range): (Index, Index) = (0, 0);
		}
	}

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
	}

	impl system::Trait for Test {
		type Origin = Origin;
		type Call = ();
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}

	impl Trait for Test {
	}

	type System = system::Module<Test>;
	type TestModule = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		let mut storage = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		storage.into()
	}

	// ------------------------------------------------------------
	// ringbuffer

	type RingBuffer = dyn RingBufferTrait<
		SomeStruct,
		Item = SomeStruct, Bounds = <TestModule as Store>::TestRange, Map = <TestModule as Store>::TestMap>;
	#[test]
	fn ringbuffer_test() {
		new_test_ext().execute_with(|| {

			let ring : Box<dyn RingBufferTrait<SomeStruct, Item = SomeStruct, Bounds = <TestModule as Store>::TestRange, Map = <TestModule as Store>::TestMap>> = Box::new(
				RingBufferTransient::<
					RingBuffer, 
					SomeStruct,
					<TestModule as Store>::TestRange,
					<TestModule as Store>::TestMap
					>::new());
			ring.push(SomeStruct{foo: 1, bar: 2});
			ring.commit();
			let start_end = TestModule::get_test_range();
			assert_eq!(start_end, (0, 1));
		})
	}

	// #[test]
	// fn ringbuffer_pop_bond() {
	// 	new_test_ext().execute_with(|| {
	// 		assert_ok!(Stablecoin::init(Origin::signed(1)));

	// 		let start_end = Stablecoin::bonds_range();
	// 		let payout = Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BaseUnit::get());
	// 		let (start, end) = Stablecoin::push_bond(start_end, Stablecoin::new_bond(2, payout));
	// 		assert_eq!(start..end, 0..1);

	// 		let ((start, end), bond) = Stablecoin::pop_bond((start, end));
	// 		assert!(bond.is_some());
	// 		assert_eq!(start..end, 1..1);
	// 	})
	// }

	// #[test]
	// fn ringbuffer_wrap_around() {
	// 	new_test_ext().execute_with(|| {
	// 		assert_ok!(Stablecoin::init(Origin::signed(1)));

	// 		let mut start_end = Stablecoin::bonds_range();
	// 		let payout = Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BaseUnit::get());
	// 		for i in 1..(u16::max_value() as u64) + 2 {
	// 			start_end = Stablecoin::push_bond(start_end, Stablecoin::new_bond(i, payout));
	// 		}
	// 		assert_eq!(
	// 			start_end,
	// 			(1, 0),
	// 			"range should be inverted because the index wrapped around"
	// 		);

	// 		let ((start, end), bond) = Stablecoin::pop_bond(start_end);
	// 		assert_eq!(start..end, 2..0);
	// 		let bond = bond.expect("a valid bond should be returned");
	// 		assert_eq!(bond.account, 2, "the bond for account 2, was placed at index 1");

	// 		let ((start, end), bond) = Stablecoin::pop_bond((start, end));
	// 		assert_eq!(start..end, 3..0);
	// 		let bond = bond.expect("a valid bond should be returned");
	// 		assert_eq!(bond.account, 3, "the bond for account 3, was placed at index 2");

	// 		start_end = (start, end);
	// 		for i in 1..4 {
	// 			start_end = Stablecoin::push_bond(start_end, Stablecoin::new_bond(i, payout));
	// 		}
	// 		assert_eq!(start_end, (4, 3));
	// 	})
	// }

	// #[test]
	// fn ringbuffer_push_front() {
	// 	new_test_ext().execute_with(|| {
	// 		assert_ok!(Stablecoin::init(Origin::signed(1)));

	// 		let start_end = Stablecoin::bonds_range();
	// 		let payout = Fixed64::from_rational(20, 100).saturated_multiply_accumulate(BaseUnit::get());
	// 		let start_end = Stablecoin::push_bond_front(start_end, Stablecoin::new_bond(2, payout));
	// 		assert_eq!(start_end, (0, 1));

	// 		let start_end = Stablecoin::push_bond_front(start_end, Stablecoin::new_bond(2, payout));
	// 		assert_eq!(start_end, (u16::max_value(), 1));
	// 	})
	// }
}
