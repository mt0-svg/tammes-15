#!/bin/sh
# Downloads the release assets listed in ASSETS.md, checks their sha256 and unpacks them into DIR.
# Usage (from the repository root): code/impl1/fetch_assets.sh DIR [TAG]   (default TAG v1.3.0)
set -eu
D=$1; TAG=${2:-v1.3.0}
U=https://github.com/mt0-svg/tammes-15/releases/download/$TAG
mkdir -p "$D"
grep -E '^[0-9a-f]{64}  ' ASSETS.md > "$D/SHA256SUMS"
cd "$D"
while read -r _ f; do [ -f "$f" ] || curl -sSfLO "$U/$f"; done < SHA256SUMS
sha256sum -c SHA256SUMS
for f in *.tar.xz; do tar xJf "$f"; done
echo "unpacked into $D: $(ls -d */ | tr '\n' ' ')"
