#!/bin/sh
# Known-answer tests of the formula; writes out/kat.out. Run: sh kat.sh
cd "$(dirname "$0")"
rm -f out/kat.out
gp -f -q -D parisizemax=1000000000 -D nbthreads=1 kat.gp < /dev/null > out/kat.out 2>&1
echo "gp exit $?" >> out/kat.out
cat out/kat.out
