`storage-adapters = '0.0.2'`
> Note: Not published to crates.io

# Transient Storage Adapters

A collection of adapters on top of the substrate storage API.

Currently implements two types of queue:
+ a bounded priority queue in the `priority_queue` module.
+ a bounded double ended queue in the `bounded_deque` module.

## Philosophy
The adapters generally try to do as few reads and writes from and to storage
as possible which is why they provide `commit` functions that are called on
`drop`.
