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

.PHONY: test-all
test-all:

.PHONY: test
test: init
	cargo test ${ARGS} -F full --  --nocapture --test-threads=1

.PHONY: build
build: init
	cargo build -F full

.PHONY: build_nostd
build_nostd: init
	cargo build --no-default-features --features full

.DEFAULT_GOAL = build

# Target name % means that it is a rule that matches anything, @: is a recipe;
# the : means do nothing
%:
	@:
