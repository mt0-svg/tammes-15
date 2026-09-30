#!/bin/sh
# Record d_range.out: d_range.gp (exact check of the enclosure), then the program's own parse
# (d_range_parse.rs, compiled against the program's iv.rs), with a header line.
# Fails on a GP error, a last GP line other than "END OK", or a Rust significand that differs.
cd "$(dirname "$0")" || exit 2
out=d_range.out
{
  echo "# code/hyps/d_range.sh, $(date -u "+%Y-%m-%d %H:%M UTC"); $(rustc --version); PARI/GP $(echo "print(version())" | gp -q -f)"
  echo "== gp -q d_range.gp"
  gp -q -D parisize=100000000 d_range.gp </dev/null 2>&1
  echo "== rustc -O d_range_parse.rs, run"
  tmp=$(mktemp -d)
  rustc -O --edition 2021 -o "$tmp/d_range_parse" d_range_parse.rs 2>&1 && "$tmp/d_range_parse"
  rm -rf "$tmp"
} >$out
g1=$(sed -n 's/^  parse_dn(dlo) = \([0-9]*\) \* 2^-53$/\1/p' $out)
g2=$(sed -n 's/^  parse_up(dhi) = \([0-9]*\) \* 2^-53$/\1/p' $out)
r1=$(sed -n 's/^dlo .* parsed = \([0-9]*\) \* 2^-53$/\1/p' $out)
r2=$(sed -n 's/^dhi .* parsed = \([0-9]*\) \* 2^-53$/\1/p' $out)
if grep -q '\*\*\*' $out || ! grep -qx 'END OK' $out || [ -z "$g1" ] || [ "$g1" != "$r1" ] || [ "$g2" != "$r2" ]; then
  echo "FAILED (see $out)" | tee -a $out
  exit 1
fi
echo "PARSE AGREES: the program's binary64 bounds are those of d_range.gp (2a)" | tee -a $out
