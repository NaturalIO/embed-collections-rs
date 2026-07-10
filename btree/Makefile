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
	cargo build --no-default-features
	cargo build --all-features

.PHONY: test
test: init
	RUST_BACKTRACE=1 cargo test ${ARGS} -- --nocapture --test-threads=1

.PHONY: test-release
test-release: init
	RUST_BACKTRACE=1 cargo test ${ARGS} --release --  --nocapture --test-threads=1

.PHONY: test-leak
test-leak:
	RUST_BACKTRACE=1 RUSTFLAGS="-Zsanitizer=leak" cargo +nightly nextest run ${ARGS} -r --no-capture -j 1

.PHONY: build_nostd
build_nostd: init
	cargo build --no-default-features --features full

.DEFAULT_GOAL = build

# Target name % means that it is a rule that matches anything, @: is a recipe;
# the : means do nothing
%:
	@:
