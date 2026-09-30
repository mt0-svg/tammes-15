#!/bin/sh
# Run check.gp at 60 digits; log in check.out, time in check.time.
# Fails on a GP error in the log or a last line other than "END OK".
cd "$(dirname "$0")" || exit 2
rm -f check.out check.time
start=$(date +%s.%N)
gp -q -D parisize=200000000 -D parisizemax=1000000000 -D nbthreads=1 -D realprecision=60 check.gp </dev/null >check.out 2>&1
st=$?
end=$(date +%s.%N)
echo "check.gp exit $st wall $(echo "$end - $start" | bc) s" >check.time
if [ $st -ne 0 ] || grep -q '\*\*\*' check.out || [ "$(tail -n 1 check.out)" != "END OK" ]; then
  echo "FAILED: check.gp (see check.out)"
  exit 1
fi
echo "passed: check.gp"
