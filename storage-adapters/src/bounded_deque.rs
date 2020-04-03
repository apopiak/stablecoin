//! # Transient BoundedDeque Implementation
//!
//! This module provides a trait and implementation for a ringbuffer that
//! abstracts over storage items and presents them as a FIFO queue.
//!
//! Usage Example:
//! ```rust,ignore
//! use storage_adapters::BoundedDeque;
//!
//! // Implementation that we will instantiate.
//! type Transient = BoundedDeque<
//!     SomeStruct,
//!     <TestModule as Store>::TestRange,
//!     <TestModule as Store>::TestMap,
//! >;
//! {
//!     let mut ring = Transient::new();
//!     ring.push_back(SomeStruct { foo: 1, bar: 2 });
//! } // `ring.commit()` will be called on `drop` here and syncs to storage
//! ```
//!
//! Note: You might want to introduce a helper function that wraps the complex
//! types and just returns the boxed trait object.

use codec::FullCodec;
use core::marker::PhantomData;
use frame_support::storage::{StorageMap, StorageValue};
use num_traits::{WrappingAdd, WrappingSub};

type DefaultIdx = u16;
/// Transient ringbuffer that sits on top of storage.
pub struct BoundedDeque<Item, B, M, Index = DefaultIdx>
where
	Item: FullCodec,
	B: StorageValue<(Index, Index), Query = (Index, Index)>,
	M: StorageMap<Index, Item, Query = Item>,
	Index: FullCodec + Eq + Ord + WrappingAdd + WrappingSub + From<u8> + Copy,
{
	start: Index,
	length: Index,
	_phantom: PhantomData<(Item, B, M)>,
}

/// Ringbuffer implementation.
impl<Item, B, M, Index> BoundedDeque<Item, B, M, Index>
where
	Item: FullCodec,
	B: StorageValue<(Index, Index), Query = (Index, Index)>,
	M: StorageMap<Index, Item, Query = Item>,
	Index: FullCodec + Eq + Ord + WrappingAdd + WrappingSub + From<u8> + Copy,
{
	/// Create a new `BoundedDeque` based on the storage types.
	///
	/// Initializes itself from the `Bounds` storage.
	pub fn new() -> BoundedDeque<Item, B, M, Index> {
		let (start, length) = B::get();
		BoundedDeque {
			start,
			length,
			_phantom: PhantomData,
		}
	}

	fn end(&self) -> Index {
		self.start.wrapping_add(&self.length)
	}

	/// Push an item onto the back of the queue.
	///
	/// + Will write over the item at the front if the queue is full.
	/// + Will insert the new item into storage, but will not update the bounds in storage.
	pub fn push_back(&mut self, item: Item) {
		let index = self.end();
		M::insert(index, item);
		// this will intentionally overflow and wrap around when the end
		// reaches `Index::max_value` because we want a ringbuffer.
		let new_end = index.wrapping_add(&Index::from(1));
		if new_end == self.start {
			// queue is full and thus writing over the front item
			self.start = self.start.wrapping_add(&Index::from(1));
		}
		// simulate saturating add
		self.length = Index::max(self.length, self.length.wrapping_add(&Index::from(1)));
	}

	/// Push an item onto the front of the queue.
	///
	/// Equivalent to `push_back` if the queue is empty.
	/// 
	/// + Will write over the item at the back if the queue is full.
	/// + Will insert the new item into storage, but will not update the bounds in storage.
	pub fn push_front(&mut self, item: Item) {
		let index = self.start.wrapping_sub(&Index::from(1));
		M::insert(index, item);
		self.start = index;
		// simulate saturating add
		self.length = Index::max(self.length, self.length.wrapping_add(&Index::from(1)));
	}

	/// Pop an item from the back of the queue.
	/// 
	/// Will remove the item from storage, but will not update the bounds in storage.
	pub fn pop_back(&mut self) -> Option<Item> {
		if self.is_empty() {
			return None;
		}
		let item = M::take(self.end().wrapping_sub(&Index::from(1)));
		self.length = self.length - Index::from(1);

		item.into()
	}

	/// Pop an item from the front of the queue.
	/// 
	/// Will remove the item from storage, but will not update the bounds in storage.
	pub fn pop_front(&mut self) -> Option<Item> {
		if self.is_empty() {
			return None;
		}
		let item = M::take(self.start);
		self.start = self.start.wrapping_add(&Index::from(1));
		self.length = self.length - Index::from(1);

		item.into()
	}

	/// Return whether to consider the queue empty.
	pub fn is_empty(&self) -> bool {
		self.length == Index::from(0)
	}

	/// Commit the (potentially) changed bounds to storage.
	pub fn commit(&self) {
		B::put((self.start, self.length));
	}
}

impl<Item, B, M, Index> Drop for BoundedDeque<Item, B, M, Index>
where
	Item: FullCodec,
	B: StorageValue<(Index, Index), Query = (Index, Index)>,
	M: StorageMap<Index, Item, Query = Item>,
	Index: FullCodec + Eq + Ord + WrappingAdd + WrappingSub + From<u8> + Copy,
{
	/// Commit on `drop`.
	fn drop(&mut self) {
		self.commit();
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use codec::{Decode, Encode};
	use frame_support::{decl_module, decl_storage, impl_outer_origin, parameter_types, weights::Weight};
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

	type TestIdx = u8;

	#[derive(Clone, PartialEq, Encode, Decode, Default, Debug)]
	pub struct SomeStruct {
		foo: u64,
		bar: u64,
	}

	decl_storage! {
		trait Store for Module<T: Trait> as RingBufferTest {
			TestMap get(fn get_test_value): map hasher(twox_64_concat) TestIdx => SomeStruct;
			TestRange get(fn get_test_range): (TestIdx, TestIdx) = (0, 0);
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

	impl Trait for Test {}

	type TestModule = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		let storage = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		storage.into()
	}

	// ------------------------------------------------------------
	// ringbuffer

	// Implementation that we will instantiate.
	type Transient = BoundedDeque<
		SomeStruct,
		<TestModule as Store>::TestRange,
		<TestModule as Store>::TestMap,
		TestIdx
	>;

	#[test]
	fn simple_push() {
		new_test_ext().execute_with(|| {
			let mut ring = Transient::new();
			ring.push_back(SomeStruct { foo: 1, bar: 2 });
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (0, 1));
			let some_struct = TestModule::get_test_value(0);
			assert_eq!(some_struct, SomeStruct { foo: 1, bar: 2 });
		})
	}

	#[test]
	fn drop_does_commit() {
		new_test_ext().execute_with(|| {
			{
				let mut ring = Transient::new();
				ring.push_back(SomeStruct { foo: 1, bar: 2 });
			}
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (0, 1));
			let some_struct = TestModule::get_test_value(0);
			assert_eq!(some_struct, SomeStruct { foo: 1, bar: 2 });
		})
	}

	#[test]
	fn simple_pop() {
		new_test_ext().execute_with(|| {
			let mut ring = Transient::new();
			ring.push_back(SomeStruct { foo: 1, bar: 2 });
			ring.push_back(SomeStruct { foo: 3, bar: 4 });
			ring.push_back(SomeStruct { foo: 5, bar: 6 });

			let item = ring.pop_front();
			assert_eq!(item, Some(SomeStruct { foo: 1, bar: 2 }));
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (1, 2));

			let item = ring.pop_back();
			assert_eq!(item, Some(SomeStruct { foo: 5, bar: 6 }));
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (1, 1));
		})
	}

	#[test]
	fn overflow_wrap_around() {
		new_test_ext().execute_with(|| {
			let mut ring = Transient::new();

			for i in 1..(TestIdx::max_value() as u64) + 2 {
				ring.push_back(SomeStruct { foo: 42, bar: i });
			}
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!(
				(start, length),
				(1, 255),
				"range should be inverted because the index wrapped around"
			);

			let item = ring.pop_front();
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (2,254));
			let item = item.expect("an item should be returned");
			assert_eq!(
				item.bar, 2,
				"the struct for field `bar = 2`, was placed at index 1"
			);

			let item = ring.pop_front();
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start,length), (3, 253));
			let item = item.expect("an item should be returned");
			assert_eq!(
				item.bar, 3,
				"the struct for field `bar = 3`, was placed at index 2"
			);

			for i in 1..4 {
				ring.push_back(SomeStruct { foo: 21, bar: i });
			}
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (4, 255));

			// push_front should overwrite the most recent entry if the queue is full
			ring.push_front(SomeStruct { foo: 4, bar: 4 });
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (3, 255));
		})
	}

	#[test]
	fn simple_push_front() {
		new_test_ext().execute_with(|| {
			let mut ring = Transient::new();
			ring.push_front(SomeStruct { foo: 1, bar: 2 });
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (TestIdx::max_value(), 1));

			ring.push_front(SomeStruct { foo: 20, bar: 42 });
			ring.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (TestIdx::max_value() - 1, 2));
		})
	}
}
