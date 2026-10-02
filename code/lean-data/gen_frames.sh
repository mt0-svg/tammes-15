#!/bin/bash
# gen_frames.sh sep|contact C1|C3: print the proof body of frameC1_sep / frameC3_sep, or frameC3_contact /
# frameC1_contact (Tammes15/Attained/Frames.lean) from the keep and contact lists of Data.lean.
#   sep: one case per ordered pair (i, j) of frame indices after `fin_cases i <;> fin_cases j`; `i ≥ j` is absurd;
#        for `i < j` the points are k1 = keep i < k2 = keep j, closed by ct_k1_k2 (a contact of the frame) or
#        sp_k1_k2 (a separation).
#   contact: one case per contact pair (i, j) of the frame, in the order of Data.lean, closed by ct_k1_k2.
# The lemma names are checked against Ident.lean and Sep.lean. Run from the repository root.
set -eu
kind=$1; c=$2; A=Tammes15/Attained
keep=$(grep "^def keep$c " $A/Data.lean | sed 's/.*!\[\(.*\)\]/\1/' | tr -d ' ')
S=$(sed -n "/^noncomputable def frame$c /,/^\$/p" $A/Data.lean | grep '  S :=' | sed 's/.*{\(.*\)}/\1/' | tr -d ' ')
IFS=, read -ra K <<< "$keep"
pairs=$(echo "$S" | sed 's/),(/ /g; s/[()]//g')
declare -A con; for p in $pairs; do con[$p]=1; done
ct() { grep -q "^theorem ct_$1_$2 " $A/Ident.lean || { echo "no ct_$1_$2" >&2; exit 1; }
  echo "inner_eq_of_num bR uR _ _ (ct_$1_$2 bR uR uR_spec.2 bR_spec.2)"; }
if [ "$kind" = contact ]; then
  n=$(echo $pairs | wc -w)
  printf '  intro ij hij\n  refine ⟨frame%s_S_ne ij hij, ?_⟩\n' "$c"
  printf '  simp only [frame%s, Finset.mem_insert, Finset.mem_singleton] at hij\n' "$c"
  printf '  rcases hij with %s\n' "$(for p in $pairs; do printf 'rfl | '; done | sed 's/ | $//')"
  for p in $pairs; do i=${p%,*}; j=${p#*,}; echo "  · exact $(ct ${K[$i]} ${K[$j]})"; done
  exit 0
fi
printf '  refine sep_of_lt bR uR keep%s ?_\n  intro i j hij\n  fin_cases i <;> fin_cases j\n' "$c"
for i in $(seq 0 14); do for j in $(seq 0 14); do
  if [ "$i" -ge "$j" ]; then echo "  · exact absurd hij (by decide)"; continue; fi
  k1=${K[$i]}; k2=${K[$j]}
  if [ -n "${con[$i,$j]:-}" ]; then echo "  · exact le_of_eq ($(ct $k1 $k2))"
  else
    grep -q "^theorem sp_${k1}_${k2} " $A/Sep.lean || { echo "no sp_${k1}_${k2}" >&2; exit 1; }
    echo "  · exact inner_le_of_num bR uR _ _ (sp_${k1}_${k2} bR uR uR_spec.1 bR_spec.1)"
  fi
done; done
