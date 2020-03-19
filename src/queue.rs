use codec::{Codec, EncodeLike};
use core::marker::PhantomData;
use frame_support::{storage::StorageValue, traits::Get};
use core::cmp::Ord;

pub trait BoundedPriorityQueueTrait<Item>
where
	Item: Codec + EncodeLike + Ord + Clone,
{
	type MaxLength: Get<usize>;

	fn commit(&mut self);
	fn push(&mut self, i: Item) -> Option<Item>;
	fn pop(&mut self) -> Option<Item>;
	fn is_empty(&self) -> bool;
}

pub struct QueueTransient<Item, Storage, MaxLength>
where
	Item: Codec + EncodeLike + Ord + Clone,
	Storage: StorageValue<Vec<Item>, Query = Vec<Item>>,
	MaxLength: Get<usize>,
{
	items: Vec<Item>,
	_phantom: PhantomData<(Storage, MaxLength)>,
}

impl<Item, Storage, MaxLength> QueueTransient<Item, Storage, MaxLength>
where
	Item: Codec + EncodeLike + Ord + Clone,
	Storage: StorageValue<Vec<Item>, Query = Vec<Item>>,
	MaxLength: Get<usize>,
{
	pub fn new() -> QueueTransient<Item, Storage, MaxLength> {
		let items = Storage::get();
		QueueTransient {
			items,
			_phantom: PhantomData,
		}
	}
}

impl<Item, Storage, MaxLength> Drop for QueueTransient<Item, Storage, MaxLength>
where
	Item: Codec + EncodeLike + Ord + Clone,
	Storage: StorageValue<Vec<Item>, Query = Vec<Item>>,
	MaxLength: Get<usize>,
{
	/// Commit on `drop`.
	fn drop(&mut self) {
		<Self as BoundedPriorityQueueTrait<Item>>::commit(self);
	}
}

impl<Item, Storage, MaxLength> BoundedPriorityQueueTrait<Item> for QueueTransient<Item, Storage, MaxLength>
where
	Item: Codec + EncodeLike + Ord + Clone,
	Storage: StorageValue<Vec<Item>, Query = Vec<Item>>,
	MaxLength: Get<usize>,
{
	type MaxLength = MaxLength;

	fn commit(&mut self) {
		Storage::put(self.items.clone());
	}

	fn push(&mut self, item: Item) -> Option<Item> {
		let index = self
			.items
			.binary_search_by(|it| it.cmp(&item))
			.unwrap_or_else(|i| i);
		self.items.insert(index, item);
		if self.items.len() > MaxLength::get() {
			return Some(self.items.remove(0));
		}
		None
	}

	fn pop(&mut self) -> Option<Item> {
		self.items.pop()
	}

	fn is_empty(&self) -> bool {
		self.items.is_empty()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use BoundedPriorityQueueTrait;

	use codec::{Decode, Encode};
	use core::cmp::Ordering;
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

	#[derive(Clone, PartialEq, Encode, Decode, Default, Debug, PartialOrd, Eq)]
	pub struct SomeStruct {
		foo: u64,
		bar: u64,
	}

	impl Ord for SomeStruct {
		fn cmp(&self, other: &Self) -> Ordering {
			self.foo.cmp(&other.foo)
		}
	}

	decl_storage! {
		trait Store for Module<T: Trait> as RingBufferTest {
			TestItems get(fn get_items): Vec<SomeStruct>;
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

	parameter_types! {
		pub const MaxLength: usize = 20;
	}

	// Trait object that we will be interacting with.
	type BoundedQueue = dyn BoundedPriorityQueueTrait<SomeStruct, MaxLength = MaxLength>;
	// Implementation that we will instantiate.
	type Transient = QueueTransient<SomeStruct, <TestModule as Store>::TestItems, MaxLength>;

	#[test]
	fn simple_push() {
		new_test_ext().execute_with(|| {
			let mut queue: Box<BoundedQueue> = Box::new(Transient::new());
			queue.push(SomeStruct { foo: 1, bar: 2 });
			queue.commit();
			let items = TestModule::get_items();
			assert_eq!(items, vec![SomeStruct { foo: 1, bar: 2 }]);
		})
	}

	#[test]
	fn simple_pop() {
		new_test_ext().execute_with(|| {
			let mut queue: Box<BoundedQueue> = Box::new(Transient::new());
			queue.push(SomeStruct { foo: 4, bar: 2 });
			queue.push(SomeStruct { foo: 1, bar: 2 });
			queue.push(SomeStruct { foo: 3, bar: 2 });

			assert_eq!(queue.pop(), Some(SomeStruct { foo: 4, bar: 2 }));
			assert_eq!(queue.pop(), Some(SomeStruct { foo: 3, bar: 2 }));
			assert_eq!(queue.pop(), Some(SomeStruct { foo: 1, bar: 2 }));
			assert_eq!(queue.pop(), None);

			queue.commit();
			assert_eq!(TestModule::get_items(), Vec::new());
		})
	}

	#[test]
	fn push_more_than_max_length() {
		new_test_ext().execute_with(|| {
			let mut queue: Box<BoundedQueue> = Box::new(Transient::new());
			let bar = 42;
			for i in 0..MaxLength::get() {
				assert_eq!(queue.push(SomeStruct { foo: i as u64, bar}), None);
			}
			assert_eq!(queue.push(SomeStruct{foo: 20, bar: 1}), Some(SomeStruct{foo: 0, bar}));
			// We get the pushed item back if we try to push onto the lowest end of a full queue.
			assert_eq!(queue.push(SomeStruct{foo: 0, bar: 2}), Some(SomeStruct{foo: 0, bar: 2}));
		})
	}
}
