#!/bin/bash
# measure-inner.sh PEAKFILE CMD... (called by measure.sh inside its scope): run CMD, then write the peak memory charge
# of the scope's cgroup to PEAKFILE; exits with CMD's status.
peak=$1; shift
rc=0; "$@" || rc=$?
cat "/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/memory.peak" > "$peak" 2> /dev/null
exit "$rc"
