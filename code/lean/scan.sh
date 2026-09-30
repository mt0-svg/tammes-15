#!/bin/bash
# Source scan: every construct that can leave a proof unfinished, bypass the kernel or change what a statement means,
# with file and line, in the .lean files and lakefile.toml given (default: Tammes15/ and lakefile.toml, from the root
# of the repository). Comments and docstrings are blanked before matching, so a construct named in a comment is not
# listed; string and char literals are read as such.
# Output: one line per source line with a construct, `file:line: construct[, construct] | code`, then a count per
# construct. Exit status 0 when nothing is found, 1 otherwise; each line is to be read (check.sh does, step 3).
set -eu
alts=(
  # proof holes
  '\bsorry\b' '\bsorryAx\b' '\badmit\b' '^[[:space:]]*stop\b'
  # trusting the compiler instead of the kernel
  'native_decide' '\+native\b' '\bnative[[:space:]]*:=' '\bofReduce(Bool|Nat)\b' '\breduce(Bool|Nat)\b' '\btrustCompiler\b'
  # declarations the kernel takes on trust, or whose runtime code differs from their definition
  '\baxiom\b' '\bopaque\b' '\bunsafe(Cast|BaseIO|EIO|IO)?\b' '\bpartial\b' '\bimplemented_by\b' '\bextern\b'
  # options that switch checks off
  '\bdebug\.[A-Za-z.]+' '\bskipKernelTC\b'
  # writes to the environment, code run at import time
  '\baddDecl\b' '\baddAndCompile\b' '\baddDeclWithoutChecking\b' '\bmodifyEnv\b' '\bsetEnv\b' '\bKernel\.Environment\b'
  '\b(builtin_)?initialize\b'
  # commands and terms that run code during elaboration
  '\brun_(tac|cmd|elab|meta)\b' '#eval' '\bby_elab\b'
  # metaprogramming: new syntax, elaborators and notation, references to the elaborator
  '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|local|scoped)[[:space:]]+)*(syntax|macro|macro_rules|elab|elab_rules|declare_syntax_cat|notation[0-9]*|infix[lr]?|prefix|postfix)\b'
  '^[[:space:]]*import[[:space:]]+Lean\b' '^[[:space:]]*open[[:space:]]+(.*[[:space:]])?Lean\b' '\bLean\.(Elab|Meta|Parser|Compiler)\b'
  # access to private declarations
  '\bopen[[:space:]]+private\b'
)
ere=$(IFS='|'; printf '%s' "${alts[*]}")
lakefile_ere='\bdebug\.[A-Za-z.]+|\bskipKernelTC\b|\b(more|weak)LeanArgs\b|\bplugins\b|\bdynlibs\b|\bprecompileModules\b'
# Blanks `-- ...` line comments and nested `/- ... -/` block comments (docstrings included) with spaces. String
# literals ("...", raw r#"..."#) and char literals are copied through, so a `--` or `/-` inside them opens nothing.
lean_code_only() {
  awk '
    BEGIN { depth = 0 }
    {
      s = $0; n = length(s); out = ""; i = 1
      while (i <= n) {
        c = substr(s, i, 1); c2 = substr(s, i, 2)
        if (depth > 0) {
          if (c2 == "/-") { depth++; out = out "  "; i += 2 }
          else if (c2 == "-/") { depth--; out = out "  "; i += 2 }
          else { out = out " "; i++ }
          continue
        }
        if (instr) {
          if (c == "\\" && !raw) { out = out c2; i += 2; continue }
          if (c == "\"" && substr(s, i + 1, rawh) == closeh) { out = out c closeh; i += 1 + rawh; instr = 0; continue }
          out = out c; i++; continue
        }
        if (c2 == "--") { out = out sprintf("%" (n - i + 1) "s", ""); break }
        if (c2 == "/-") { depth = 1; out = out "  "; i += 2; continue }
        prev = (i > 1) ? substr(s, i - 1, 1) : " "
        idch = (prev ~ /[A-Za-z0-9_.!?\047]/)
        if (c == "\"") { instr = 1; raw = 0; rawh = 0; closeh = ""; out = out c; i++; continue }
        if (c == "r" && !idch && match(substr(s, i + 1), /^#*"/)) {
          rawh = RLENGTH - 1; closeh = substr(s, i + 1, rawh); instr = 1; raw = 1
          out = out substr(s, i, RLENGTH + 1); i += RLENGTH + 1; continue
        }
        if (c == "\047" && !idch && match(substr(s, i), /^\047(\\[^\047]+|[^\\\047])\047/)) {
          out = out substr(s, i, RLENGTH); i += RLENGTH; continue
        }
        out = out c; i++
      }
      print out
    }'
}
[ $# -gt 0 ] || set -- Tammes15 lakefile.toml
files=$(for p in "$@"; do
  if [ -d "$p" ]; then find "$p" \( -name .lake -o -name .git \) -prune -o -type f \( -name '*.lean' -o -name lakefile.toml \) -print
  else printf '%s\n' "$p"; fi
done | LC_ALL=C sort -u)
hits=$(mktemp); trap 'rm -f "$hits"' EXIT
nfiles=$(printf '%s\n' "$files" | wc -l)
while IFS= read -r f; do
  if [ "${f##*/}" = lakefile.toml ]; then re=$lakefile_ere; filt=(sed 's/#.*//'); else re=$ere; filt=(lean_code_only); fi
  "${filt[@]}" < "$f" | grep -nE "$re" | while IFS= read -r l; do
    ln=${l%%:*}; code=${l#*:}
    toks=$(printf '%s\n' "$code" | grep -oE "$re" | awk '
      { t = $0; sub(/^[[:space:]]+/, "", t)
        if (t ~ /^native[[:space:]]*:=/) t = "native :="
        else if (t ~ /^import[[:space:]]/) t = "import Lean"
        else if (t ~ /^open[[:space:]]+private/) t = "open private"
        else if (t ~ /^open[[:space:]]/) t = "open Lean"
        else if (t ~ /^@\[/ || t ~ /[[:space:]]/) { n = split(t, w, /[[:space:]]+/); t = w[n] }
        gsub(/[[:space:]]+/, " ", t); printf "%s%s", (NR > 1 ? ", " : ""), t }')
    code=$(printf '%s' "$code" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//' | cut -c1-160)
    printf '%s:%s: %s | %s\n' "$f" "$ln" "$toks" "$code"
  done
done <<< "$files" | tee "$hits"
n=$(wc -l < "$hits")
if [ "$n" -eq 0 ]; then echo "SCAN: no construct in $nfiles files"; exit 0; fi
echo "SCAN: $n lines with a construct in $nfiles files; per construct:"
sed -E 's/^[^:]*:[0-9]+: //; s/ \| .*$//' "$hits" | tr ',' '\n' | sed 's/^ //' | sort | uniq -c | sort -rn
exit 1
