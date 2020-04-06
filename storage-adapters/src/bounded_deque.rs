//! # Transient Bounded Deque Implementation
//!
//! This module provides an implementation of a bounded FIFO double ended
//! queue built on top of a ringbuffer that abstracts over a storage map.
//! 
//! The queue is bounded to the maximum amount of values that can be indexed
//! with the provided `Index` type. So a queue with a `u8` index will be limited
//! to `u8::max_value() + 1 == 256` values.
//! 
//! The queue eagerly inserts and removes values from its underlying storage map
//! but lazily stores the bounds on `drop` or (explicit calls to) `commit`.
//!
//! Usage Example:
//! ```rust,ignore
//! use storage_adapters::BoundedDeque;
//!
//! // Implementation that we will instantiate.
//! type Queue = BoundedDeque<
//!     SomeStruct,
//!     <TestModule as Store>::TestRange,
//!     <TestModule as Store>::TestMap,
//! >;
//! {
//!     let mut queue = Queue::new();
//!     queue.push_back(SomeStruct { foo: 1, bar: 2 });
//! } // `queue.commit()` will be called on `drop` here and syncs the bounds to storage.
//! ```
//!
//! Note: You might want to introduce a helper function that wraps the complex
//! type and just returns the object.

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

	/// Create a new `BoundedDeque` based on passed bounds.
	/// 
	/// Bounds are assumed to be valid.
	pub fn from_bounds(start: Index, length: Index) -> BoundedDeque<Item, B, M, Index> {
		BoundedDeque {
			start,
			length,
			_phantom: PhantomData,
		}
	}

	/// Get the index past the last element.
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

	/// Commit the potentially changed bounds to storage.
	/// 
	/// Note: Is called on `drop`, so usually does need to be called explicitly.
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

	// Implementation that we will instantiate.
	type Queue = BoundedDeque<
		SomeStruct,
		<TestModule as Store>::TestRange,
		<TestModule as Store>::TestMap,
		TestIdx
	>;

	#[test]
	fn construction() {
		new_test_ext().execute_with(|| {
			<TestRange>::put((5, 2));
			let queue = Queue::new();
			// bounds are initialized from storage
			assert_eq!(queue.start, 5);
			assert_eq!(queue.length, 2);

			let queue = Queue::from_bounds(3, 4);
			assert_eq!(queue.start, 3);
			assert_eq!(queue.length, 4);
			// bounds are not changed in storage when initializing from bounds
			assert_eq!(TestModule::get_test_range(), (5, 2));
			queue.commit();
			// bounds are updated on commit
			assert_eq!(TestModule::get_test_range(), (3, 4));
		})
	}

	#[test]
	fn simple_push() {
		new_test_ext().execute_with(|| {
			let mut queue = Queue::new();
			queue.push_back(SomeStruct { foo: 1, bar: 2 });
			queue.commit();
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
				let mut queue = Queue::new();
				queue.push_back(SomeStruct { foo: 1, bar: 2 });
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
			let mut queue = Queue::new();
			queue.push_back(SomeStruct { foo: 1, bar: 2 });
			queue.push_back(SomeStruct { foo: 3, bar: 4 });
			queue.push_back(SomeStruct { foo: 5, bar: 6 });

			let item = queue.pop_front();
			assert_eq!(item, Some(SomeStruct { foo: 1, bar: 2 }));
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (1, 2));

			let item = queue.pop_back();
			assert_eq!(item, Some(SomeStruct { foo: 5, bar: 6 }));
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (1, 1));
		})
	}

	#[test]
	fn overflow_wrap_around() {
		new_test_ext().execute_with(|| {
			let mut queue = Queue::new();

			for i in 1..(TestIdx::max_value() as u64) + 2 {
				queue.push_back(SomeStruct { foo: 42, bar: i });
			}
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!(
				(start, length),
				(1, 255),
				"range should be inverted because the index wrapped around"
			);

			let item = queue.pop_front();
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (2,254));
			let item = item.expect("an item should be returned");
			assert_eq!(
				item.bar, 2,
				"the struct for field `bar = 2`, was placed at index 1"
			);

			let item = queue.pop_front();
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start,length), (3, 253));
			let item = item.expect("an item should be returned");
			assert_eq!(
				item.bar, 3,
				"the struct for field `bar = 3`, was placed at index 2"
			);

			for i in 1..4 {
				queue.push_back(SomeStruct { foo: 21, bar: i });
			}
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (4, 255));

			// push_front should overwrite the most recent entry if the queue is full
			queue.push_front(SomeStruct { foo: 4, bar: 4 });
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (3, 255));
		})
	}

	#[test]
	fn simple_push_front() {
		new_test_ext().execute_with(|| {
			let mut queue = Queue::new();
			queue.push_front(SomeStruct { foo: 1, bar: 2 });
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (TestIdx::max_value(), 1));

			queue.push_front(SomeStruct { foo: 20, bar: 42 });
			queue.commit();
			let (start, length) = TestModule::get_test_range();
			assert_eq!((start, length), (TestIdx::max_value() - 1, 2));
		})
	}
}
