#!/bin/bash
# Regenerate the vendored files with vendor.sh into a temporary directory and compare them with
# Tammes15/Vendor/EM8; the expected output ends with "REGEN IDENTICAL".
# Run: EM8_SRC=<clone>/LeanCode/LargeS/Lean_Code bash code/vendor/regen_check.sh > code/vendor/regen_check.out
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
VENDOR_DST=$tmp/EM8 bash "$HERE/vendor.sh" | sed "s|$tmp|<tmp>|"
echo "files: $(ls "$tmp/EM8" | wc -l) regenerated, $(ls "$HERE/../../Tammes15/Vendor/EM8" | wc -l) in Tammes15/Vendor/EM8"
if diff -r "$tmp/EM8" "$HERE/../../Tammes15/Vendor/EM8"; then echo "REGEN IDENTICAL"; else echo "REGEN DIFFERS"; fi
