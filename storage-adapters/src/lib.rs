//! # Transient Storage Adapters
//!
//! A collection of adapters on top of the substrate storage API.
//!
//! Currently implements a bounded priority queue in the `priority_queue` module.
//! Implements a ringbuffer queue in the `ringbuffer` module.

pub mod priority_queue;
pub mod ringbuffer;

pub use priority_queue::BoundedPriorityQueue;
pub use ringbuffer::BoundedDequeue;
