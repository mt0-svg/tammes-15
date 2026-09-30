#!/bin/sh
# Table of a replay_all.sh run: job, verified, failed, missing, wall seconds, user seconds.
O=$1
printf '%-16s %9s %6s %7s %9s %9s\n' job verified failed missing wall_s user_s
for l in "$O"/*.log; do
  n=$(basename "$l" .log)
  set -- $(sed -n 's/^replay: verified \([0-9]*\) failed \([0-9]*\) missing certificates \([0-9]*\).*/\1 \2 \3/p' "$l") - - -
  tm=$(cat "$O/$n.time" 2>/dev/null | tail -1)
  printf '%-16s %9s %6s %7s %9s %9s\n' "$n" "$1" "$2" "$3" ${tm:-- -}
done
awk 'FNR == 1 {next} {v += $2; f += $3; w += $5; u += $6} END {printf "%-16s %9d %6d %7s %9.0f %9.0f\n", "total", v, f, "", w, u}' <<X
$(for l in "$O"/*.log; do n=$(basename "$l" .log); set -- $(sed -n 's/^replay: verified \([0-9]*\) failed \([0-9]*\) missing certificates \([0-9]*\).*/\1 \2 \3/p' "$l") 0 0 0; echo "$n $1 $2 $3 $(tail -1 "$O/$n.time" 2>/dev/null || echo 0 0)"; done | sed '1i header')
X
