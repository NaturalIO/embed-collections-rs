# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### Added

### Removed

### Changed

### Fixed

## [0.12.4] - 2026-06-23

### Added

- irc: Add Irc::with_unchecked()

## [0.12.3] - 2026-06-01

### Added

- various: Add prepend()

- various_map: Add remove()

## [0.12.2] - 2026-05-25

- irc: Change the IrcItem trait to support custom container, backward compatible with default param

## [0.12.1] - 2026-05-22

### Added

- Add Irc (intrusive ref count) gated by `irc` feature

## [0.12.0] - 2026-05-21

### Changed

- Add feature gate "seglist" & "various"

## [0.11.6] - 2026-05-14

### Added

- various_map: Add missing IntoIter for &VariousMap

## [0.11.5] - 2026-05-13

### Added

- various_map: Add keys(), values(), values_mut(), iter_mut()

## [0.11.4] - 2026-05-10

### Fixed

- avl: Add trait requirement to AvlNode struct

- seg_list: Fix missing Send in iterators

- btree: Fix missing Send in iterators

## [0.11.3] - 2026-05-07

### Fixed

- btree: Fix debug assert when tree split

## [0.11.2] - 2026-05-01

### Fixed

- VariousMap: Fix Entry unnecessary Default requirement

## [0.11.1] - 2026-05-01

### Added

- VariousMap: impl ExactSizeIterator & DoubleEndedIterator

## [0.11.0] - 2026-05-01

### Added

- Add VariousMap (a temporary map wraps std BTreeMap with `Option<(K, V)>` to delay allocation)

## [0.10.0] - 2026-04-28

### Added

- avl: Add iter() & iter_rev(), support iterate &P::Target and get &P through next_ref()

- btree: Add remove_entry()

- Add SmartPointer trait

- impl Pointer for &T

- Pointer trait add as_ptr()

- avl: Add missing Send

### Changed

- avl: Move cmp function into AvlItem trait, support borrow_key() and Ord

- avl: Change get_count() to len()

### Removed

- avl: wake() is replace by iter()

## [0.9.0] - 2026-04-26

### Added

- btree: Add readonly Cursor

### Changed

- btree: Fix typo in API, "peak" rename to "peek"

## [0.8.4] - 2026-04-24

### Fixed

- btree: Fix alter_key() when:
  - TreeInfo may not exist (height=1)
  - alter_key should fix cache position to the center (for peak_ancestor)

## [0.8.3] - 2026-04-24 (yanked)

### Fixed

- btree: Fix entry remove following move_forward/backward (will broken tree structure)

### Changed

- btree: Reduce struct size to 24B (the same with std)

- btree: Smart optimization for sequential & random insertion

### Added

- btree: expose leaf_count() & inter_count() and memory_used()

## [0.8.2] - 2026-04-19 (yanked)

### Added

- btree: Add IntoIter::rev() and BTreeMap::into_iter_rev()

### Fixed

- btree: Fix for zero-sized value

- btree: Enhance search speed (insert/get)

## [0.8.1] - 2026-04-19 (yanked)

### Changed

- btree: Minor optimize in `remove_range()`

### Fixed

- btree: Fix doc link

## [0.8.0] - 2026-04-19 (yanked)

### Added

- btree: A b+tree implementation with special api

## [0.7.2] - 2026-04-06

### Added

- seg_list & various: Add iter_rev(), iter_mut_rev(), into_rev()

## [0.7.1] - 2026-03-29

### Added

- Various: Add clear method

## [0.7.0] - 2026-03-19

### Changed

- seg_list: Optimize drain operation and allocation strategy. Added benchmark result.

- Add more example for dlist & slist using various type

## [0.6.0] - 2026-03-18

### Added

- Impl Pointer for `*mut T`

- dlist: Expose remove_node() to remove node from the middle of the list.

### Changed

- dlist: change peak() signature to reference.

### Fixed

- ConstVec: Fix miri warning

## [0.5.2] - 2026-03-17

### Changed

- Remove `full` feature flag from default

## [0.5.1] - 2026-03-11

### Changed

- SegList: Ensure at least 2 items when T is large.

## [0.5.0] - 2026-03-10

### Added

- Add ConstVec: Fixed capacity inline vec

- Add SegList:  A list to store elements with fixed size segments (the capacity of segment is calculated to fit a CPU cacheline)

- Add Various: For various count of elements passing between functions, zero or one condition will use Option, otherwise will using `SegList`

### Removed

- RangeTree is removed and moved to crate range-tree-rs

## [0.4.1] - 2026-03-09

### Changed

- Fix clippy warning

### Removed

- slist & dlist: Remove unused get_length(). length field changed to usize

## [0.4.0] - 2026-02-24

### Changed

- range_tree: Reduce RangeTreeSimple size, remove unused stats fields

- range_tree: Remove explicit set_ops(), ops should be init with Default

- range_tree: Reduce RangeSeg size for RangeTreeSimple

## [0.3.0] - 2026-01-31

### Fixed

- Fix SLinkedList::clear & DLinkedList::clear

### Added

- Add SLinkedList::push_front

- Add SLinkedListOwned

## [0.2.4] - 2026-01-29

### Fixed

- range_tree: Fix missing Send on iterator and RangeSeg

## [0.2.2] - 2026-01-29

### Added

- Add iterator for RangeTree

## [0.2.0] - 2026-01-26

### Added

- Add avl and range tree ported from ZFS

## [0.1.5] - 2026-01-24

### Fixed

- Fix dlist::drain() order to FIFO

## [0.1.2] - 2025-12-25

### Added

- Add no-std support
