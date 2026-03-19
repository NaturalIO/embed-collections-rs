# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### Added

### Removed

### Changed

### Fixed

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
