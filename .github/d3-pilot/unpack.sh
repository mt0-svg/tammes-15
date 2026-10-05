#!/bin/bash
# unpack.sh FILE KIND JOB: check the asset FILE of chunk job JOB against its sha256 line in
# .github/d3-pilot/ASSETS.sha256, check its paths, and unpack it at the root of the package. KIND data: the tarball
# d3-pilot-JOB.tar.xz, the generated data modules, every path under D3E2E/. KIND stmt: the tarball
# d3-pilot-JOB-stmt.tar.xz, the loader modules of the job's statement, exactly the files
# Tammes15/D3Pilot/Jobs/JOB/<name>.lean that the commit's Tammes15/D3Pilot/Jobs/JOB.lean imports, nothing else, none
# present before. Both kinds: only plain files and directories, no absolute path, no ".." component. Fails on any
# mismatch, before anything is built.
set -euo pipefail
file=$1; kind=$2; job=$3
case $kind in
  data) f=d3-pilot-$job.tar.xz ;;
  stmt) f=d3-pilot-$job-stmt.tar.xz ;;
  *) echo "unknown kind $kind"; exit 1 ;;
esac
want=$(awk -v f="$f" '$2 == f {print $1}' .github/d3-pilot/ASSETS.sha256)
[ -n "$want" ] || { echo "no sha256 line for $f in .github/d3-pilot/ASSETS.sha256"; exit 1; }
got=$(sha256sum < "$file" | cut -d' ' -f1)
echo "$f: sha256 $got, expected $want"
[ "$got" = "$want" ] || { echo "$f: sha256 mismatch"; exit 1; }
paths=$(xz -d -T0 -c "$file" | tar -t)
odd=$(xz -d -T0 -c "$file" | tar -tv | awk '$1 !~ /^[-d]/' | wc -l)
[ "$odd" = 0 ] || { echo "$f: $odd entries neither plain files nor directories"; exit 1; }
up=$(printf '%s\n' "$paths" | grep -c -e '^/' -e '(^|/)\.\.(/|$)' -E || true)
[ "$up" = 0 ] || { echo "$f: $up absolute paths or paths with .."; exit 1; }
if [ "$kind" = data ]; then
  bad=$(printf '%s\n' "$paths" | grep -cv '^D3E2E/' || true)
  [ "$bad" = 0 ] || { echo "$f: $bad paths outside D3E2E/"; exit 1; }
else
  d=Tammes15/D3Pilot/Jobs/$job
  [ ! -e "$d" ] || { echo "$d exists before the asset is unpacked"; exit 1; }
  expect=$(sed -n "s#^import Tammes15\.D3Pilot\.Jobs\.$job\.\([A-Za-z0-9_]*\)\$#$d/\1.lean#p" "Tammes15/D3Pilot/Jobs/$job.lean" | LC_ALL=C sort)
  [ -n "$expect" ] || { echo "Tammes15/D3Pilot/Jobs/$job.lean imports no loader module"; exit 1; }
  if [ "$(printf '%s\n' "$paths" | LC_ALL=C sort)" != "$expect" ]; then
    echo "$f: its files are not exactly the loader modules imported by Tammes15/D3Pilot/Jobs/$job.lean"
    diff <(printf '%s\n' "$paths" | LC_ALL=C sort) <(printf '%s\n' "$expect") | head -20
    exit 1
  fi
fi
xz -d -T0 -c "$file" | tar -x --no-same-owner
echo "$f: unpacked $(printf '%s\n' "$paths" | wc -l) files"
