#!/bin/sh
# Usage: params.sh DLO DHI > params.txt   (degrees, exact rationals such as 571367/10000)
d=$(dirname "$0")
{ printf 'DLO=%s;DHI=%s;\n' "$1" "$2"; cat "$d/consts.gp"; } > /tmp/tammes_consts_$$.gp
gp -q /tmp/tammes_consts_$$.gp < /dev/null 2>/dev/null | grep -v -E 'realprecision|Warning'
rm -f /tmp/tammes_consts_$$.gp
