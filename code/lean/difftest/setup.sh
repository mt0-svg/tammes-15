#!/usr/bin/env bash
# Builds the program under test for the differential test (Section 9.3 of the paper): a copy of code/impl1/rust
# (with its two guards, code/impl1/deep-guards.patch, the program that Tammes15/Contractors/Prims.lean transcribes),
# with logging.patch (the operations of ivt.rs and iv.rs record their arguments and results, values unchanged) and
# the driver. The copy is made in build/ (ignored by git).
# Usage: code/lean/difftest/setup.sh   (build/impl1, then cargo build --release --offline, one job); then
#        (cd code/lean/difftest/lean && lake build difftest soundcheck) for the Lean side.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=$here/../../impl1/rust
dst=$here/build/impl1
rm -rf "$dst"
mkdir -p "$dst/src/bin"
cp "$src"/src/*.rs "$dst/src/"
cp "$here/Cargo.toml.copy" "$dst/Cargo.toml"
patch -s -d "$dst" -p1 < "$here/logging.patch"
cp "$here/dtlog.rs" "$dst/src/dtlog.rs"
cp "$here/driver.rs" "$dst/src/dt_driver.rs"
printf 'fn main() {\n    tammes15::deep::dt_driver::main();\n}\n' > "$dst/src/bin/difftest.rs"
cd "$dst"
CARGO_TARGET_DIR=$here/build/target cargo build --release --offline -j 1
