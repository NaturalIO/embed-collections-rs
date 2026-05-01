#!/bin/bash

cargo clippy -F full -- -D warnings || exit 1
cargo install cargo-rdme
cargo rdme --check || exit 1
cargo publish
