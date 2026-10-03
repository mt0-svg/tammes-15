#!/bin/bash
# gen_tiedata.sh [IN [OUT]]: Tammes15/PaperSteps/TieData.lean (or OUT) from data/tie_targets.txt (or IN), the file
# of targets that the program reads (code/impl1/rust/src/local.rs, Targets::load). The numbers are copied as
# written: per configuration, 15 lines of "x_mid x_rad y_mid y_rad z_mid z_rad" and the line "contacts i j i j ..."
# (0-based, 30 pairs). Run from the repository root; code/lean-data/regen.sh compares OUT with the Lean file.
set -eu
IN=${1:-data/tie_targets.txt}
OUT=${2:-Tammes15/PaperSteps/TieData.lean}
awk '
  /^#/ || NF == 0 { next }
  /^conf / { nc++; name[nc] = substr($0, 6); np = 0; next }
  /^contacts / { if (NF != 61) { print "bad contacts line" > "/dev/stderr"; exit 1 }
    s = ""; for (i = 2; i <= 60; i += 2) s = s (i > 2 ? ", " : "") "(" $i ", " $(i + 1) ")"; con[nc] = s; next }
  NF == 6 { np++; for (k = 0; k < 3; k++) { mid[nc, np, k] = $(2 * k + 1); rad[nc, np, k] = $(2 * k + 2) }; next }
  { print "unexpected line: " $0 > "/dev/stderr"; exit 1 }
  END {
    if (nc != 8) { print "expected 8 configurations" > "/dev/stderr"; exit 1 }
    print "import Mathlib.Basic.Real.Basic"
    print "import Mathlib.Data.Fin.VecNotation"
    print ""
    print "/-!"
    print "# The targets of Local, as the program reads them (generated)"
    print ""
    print "Written by gen_tiedata.sh from tie_targets.txt, the file of targets that the program reads: the"
    print "eight frame configurations, each with 15 points given by a midpoint and a"
    print "radius per coordinate, and its 30 contacts (0-based). Configurations in file order:"
    for (c = 1; c <= nc; c++) print "`" c - 1 "`: " name[c] (c < nc ? ";" : ".")
    print "-/"
    print ""
    print "namespace Tammes15.PaperSteps"
    print ""
    print "/-- Midpoints of the target coordinates: configuration, point, coordinate. -/"
    print "def tieMid : Fin 8 → Fin 15 → Fin 3 → ℝ := !["
    for (c = 1; c <= nc; c++) { print "  !["
      for (p = 1; p <= 15; p++) printf "    ![%s, %s, %s]%s\n", mid[c, p, 0], mid[c, p, 1], mid[c, p, 2], (p < 15 ? "," : "")
      print "  ]" (c < nc ? "," : "") }
    print "]"
    print ""
    print "/-- Radii of the target coordinates: configuration, point, coordinate. -/"
    print "def tieRad : Fin 8 → Fin 15 → Fin 3 → ℝ := !["
    for (c = 1; c <= nc; c++) { print "  !["
      for (p = 1; p <= 15; p++) printf "    ![%s, %s, %s]%s\n", rad[c, p, 0], rad[c, p, 1], rad[c, p, 2], (p < 15 ? "," : "")
      print "  ]" (c < nc ? "," : "") }
    print "]"
    print ""
    print "/-- The 30 contacts of each configuration, as listed (0-based point indices). -/"
    print "def tieContacts : Fin 8 → List (Fin 15 × Fin 15) := !["
    for (c = 1; c <= nc; c++) print "  [" con[c] "]" (c < nc ? "," : "")
    print "]"
    print ""
    print "end Tammes15.PaperSteps"
  }' "$IN" > "$OUT"
echo "wrote $OUT ($(wc -l < "$OUT") lines)"
