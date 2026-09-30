#!/bin/bash
# Prints the source hash of the header of code/lean/check.out for the files of this checkout, from the root of the
# repository: the sha256 of the list of sha256 sums of Tammes15/, lakefile.toml, lake-manifest.json, lean-toolchain
# and the five files of code/lean/ that check.sh reads. The same value means the checks ran on these sources.
set -eu
cd "$(dirname "$0")/../.."
{ find Tammes15 -type f; printf '%s\n' lakefile.toml lake-manifest.json lean-toolchain code/lean/{check.sh,scan.sh,axioms.lean,types.lean,EnvAudit.lean}; } \
  | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -c1-16
