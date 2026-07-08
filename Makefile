# filter out target and keep the rest as args
PRIMARY_TARGET := $(firstword $(MAKECMDGOALS))
ARGS := $(filter-out $(PRIMARY_TARGET), $(MAKECMDGOALS))

.PHONY: git-hooks
git-hooks:
	git config core.hooksPath ./git-hooks;

.PHONY: init
init: git-hooks

.PHONY: fmt
fmt: init
	cargo fmt

.PHONY: build
build: init
	cargo build --no-default-features -p embed-avl
	cargo build --no-default-features -p embed-btree
	cargo build --no-default-features -p embed-constvec
	cargo build --no-default-features -p embed-dlist
	cargo build --no-default-features -p embed-seglist
	cargo build --no-default-features -p embed-slist
	cargo build --all-features -p embed-avl
	cargo build --all-features -p embed-btree
	cargo build --all-features -p embed-constvec
	cargo build --all-features -p embed-dlist
	cargo build --all-features -p embed-seglist
	cargo build --all-features -p embed-slist

.PHONY: clippy
clippy: init
	cargo clippy -p embed-avl -- -D warnings
	cargo clippy -p embed-btree -- -D warnings
	cargo clippy -p embed-constvec -- -D warnings
	cargo clippy -p embed-dlist -- -D warnings
	cargo clippy -p embed-seglist -- -D warnings
	cargo clippy -p embed-slist -- -D warnings

.PHONY: test
test: init
	cd avl; make test;
	cd btree; make test;
	cd constvec; make test;
	cd dlist; make test;
	cd seglist; make test;
	cd slist; make test;

.PHONY: test-release
test-release: init
	cd avl; make test-release;
	cd btree; make test-release;
	cd constvec; make test-release;
	cd dlist; make test-release;
	cd seglist; make test-release;
	cd slist; make test-release;

test-leak:
	cd avl; make test-leak;
	cd btree; make test-leak;
	cd constvec; make test-leak;
	cd dlist; make test-leak;
	cd seglist; make test-leak;
	cd slist; make test-leak;

.DEFAULT_GOAL = build

# Target name % means that it is a rule that matches anything, @: is a recipe;
# the : means do nothing
%:
	@:
