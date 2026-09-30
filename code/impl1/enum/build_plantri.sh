#!/bin/sh
# Downloads plantri 5.8 (G. Brinkmann and B. D. McKay, https://users.cecs.anu.edu.au/~bdm/plantri/,
# Apache License 2.0), checks its sha256, and builds plantri and plantri_md5 (plantri with the
# output filter plantri_md5.c: maximum degree <= 5) into code/impl1/enum/bin.
# Usage (from the repository root): sh code/impl1/enum/build_plantri.sh
set -eu
D=code/impl1/enum
SUM=e78a944116fec9f2c9f5e484206276cc2b0043bae803e9815f4b2683614629b8
mkdir -p "$D/build" "$D/bin"
cd "$D/build"
[ -f plantri58.tar.gz ] || curl -sSfLO https://users.cecs.anu.edu.au/~bdm/plantri/plantri58.tar.gz
echo "$SUM  plantri58.tar.gz" | sha256sum -c -
tar xzf plantri58.tar.gz
cd plantri58
cp ../../plantri_md5.c .
cc -O3 -o ../../bin/plantri plantri.c
cc -O3 -o ../../bin/plantri_md5 -DPLUGIN=plantri_md5.c plantri.c
echo "built $D/bin/plantri and $D/bin/plantri_md5"
