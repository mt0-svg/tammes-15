#!/bin/sh
# Builds plantri_ms (plantri 5.8 with the plugin plantri_ms.c) and plantri_ms_chk (the same with
# -DMS_CHECK) into BUILD (default build/ here), as the release builds plantri_md5: the plantri58
# tarball checked by sha256, cc -O3. Prints the sha256 of the tarball, plantri.c, the plugin and the
# binaries. The tarball is taken from $PLANTRI_TGZ if set, else downloaded.
# Usage: sh build.sh [BUILD]
set -eu
D=$(cd "$(dirname "$0")" && pwd)
B=${1:-$D/build}
SUM=e78a944116fec9f2c9f5e484206276cc2b0043bae803e9815f4b2683614629b8
mkdir -p "$B"
cd "$B"
if [ ! -f plantri58.tar.gz ]; then
  if [ -n "${PLANTRI_TGZ:-}" ]; then cp "$PLANTRI_TGZ" plantri58.tar.gz
  else curl -sSfLO https://users.cecs.anu.edu.au/~bdm/plantri/plantri58.tar.gz; fi
fi
echo "$SUM  plantri58.tar.gz" | sha256sum -c -
rm -rf plantri58
tar xzf plantri58.tar.gz
cp "$D/plantri_ms.c" plantri58/
cd plantri58
cc -O3 -o ../plantri_ms -DPLUGIN=plantri_ms.c plantri.c
cc -O3 -DMS_CHECK -o ../plantri_ms_chk -DPLUGIN=plantri_ms.c plantri.c
cd ..
echo "cc: $(cc --version | head -1)"
grep '^#define VERSION' plantri58/plantri.c
sha256sum plantri58.tar.gz plantri58/plantri.c plantri58/plantri_ms.c plantri_ms plantri_ms_chk | sed "s|  .*/|  |"
