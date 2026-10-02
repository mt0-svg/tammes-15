#!/bin/bash
# gen_roots2.sh [OUT [TIEMAP]]: Tammes15/PaperSteps/Roots2.lean (or OUT) from Tammes15/PaperSteps/TieMap.lean (or
# TIEMAP), the tight enclosures of uR and bR (TieMap: ul2, uh2, bl2, bh2) and the nine coordinate values aN .. tN of
# the frame within 1e-39 of the data midpoints (rows 0, 3 and 6 of ptMid), by dyadic_interval as in
# Attained/Roots.lean and Kappa/Close.lean. Run from the repository root; code/lean-data/regen.sh compares OUT with
# the Lean file.
set -eu
L=Tammes15/PaperSteps
OUT=${1:-$L/Roots2.lean}
TM=${2:-$L/TieMap.lean}
vals=$(awk '/^def ptMid/{on=1;next} on && /^  !\[/{n++; s=$0; gsub(/^  !\[|\],?$|\]\]$/,"",s); row[n]=s} END{print row[1] ", " row[4] ", " row[7]}' "$TM" | tr -d ' ')
IFS=',' read -r -a M <<< "$vals"
[ ${#M[@]} -eq 9 ] || { echo "expected 9 values" >&2; exit 1; }
names=(aN bN cN dN eN fN rN sN tN)
{
cat <<'EOF'
import Tammes15.Attained.Roots
import Tammes15.PaperSteps.TieMap

/-!
# Tight enclosures of `uR` and `bR`, and the frame coordinates to `1e-39` (generated)

Written by gen_roots2.sh from TieMap.lean. `uR ∈ [ul2, uh2]` by the sign change of the quintic
and the uniqueness of its root in `(1/2, 7/10)` (`existsUnique_root`); `bR ∈ [bl2, bh2]` by the
sign change of `Q4 · uR` and its strict monotonicity on `[bl, bh]` (`Q4_strictMonoOn`). On these
enclosures each coordinate value `xN b u / 225008` of the frame is within `1e-39` of the midpoint
of the targets that stands for it (`close_aN` to `close_tN`).
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace Tammes15.PaperSteps

open Tammes15 Attained

theorem quintic_lo2 : quintic ul2 < 0 := by
  norm_num [quintic, ul2]

theorem quintic_hi2 : 0 < quintic uh2 := by
  norm_num [quintic, uh2]

theorem Q4_lo2 (u : ℝ) (hu : u ∈ Set.Icc ul2 uh2) : Q4 bl2 u < 0 := by
  simp only [ul2, uh2] at hu
  simp only [Q4, bl2]
  dyadic_interval [prec := 400]

theorem Q4_hi2 (u : ℝ) (hu : u ∈ Set.Icc ul2 uh2) : 0 < Q4 bh2 u := by
  simp only [ul2, uh2] at hu
  simp only [Q4, bh2]
  dyadic_interval [prec := 400]

/-- The coefficient of `b⁴` in `Q4 b u`. -/
def q4A (u : ℝ) : ℝ := 324 * u * u * u * u + 135 * u * u * u - 99 * u * u - 63 * u - 9

/-- The coefficient of `b²` in `Q4 b u`. -/
def q4B (u : ℝ) : ℝ :=
  124 * u * u * u * u * u - 310 * u * u * u * u - 74 * u * u * u + 102 * u * u + 30 * u

/-- The difference of `Q4` in `b`, factored. -/
theorem Q4_sub (b₁ b₂ u : ℝ) :
    Q4 b₂ u - Q4 b₁ u = (b₂ - b₁) * ((b₂ + b₁) * (q4A u * (b₂ * b₂ + b₁ * b₁) + q4B u)) := by
  unfold Q4 q4A q4B
  ring

theorem Q4_slope_pos (b₁ b₂ u : ℝ) (hu : u ∈ Set.Icc ul uh) (h₁ : b₁ ∈ Set.Icc bl bh)
    (h₂ : b₂ ∈ Set.Icc bl bh) : 0 < (b₂ + b₁) * (q4A u * (b₂ * b₂ + b₁ * b₁) + q4B u) := by
  simp only [ul, uh, bl, bh] at hu h₁ h₂
  simp only [q4A, q4B]
  dyadic_interval [prec := 100]

theorem Q4_strictMonoOn (u : ℝ) (hu : u ∈ Set.Icc ul uh) :
    StrictMonoOn (fun b => Q4 b u) (Set.Icc bl bh) := by
  intro b₁ h₁ b₂ h₂ hlt
  have h := Q4_sub b₁ b₂ u
  have hp := Q4_slope_pos b₁ b₂ u hu h₁ h₂
  have : 0 < Q4 b₂ u - Q4 b₁ u := by
    rw [h]
    exact mul_pos (by linarith) hp
  show Q4 b₁ u < Q4 b₂ u
  linarith

theorem uR_mem2 : uR ∈ Set.Icc ul2 uh2 := by
  obtain ⟨u', hu', hq⟩ : ∃ u' ∈ Set.Icc ul2 uh2, quintic u' = 0 := by
    have hle : ul2 ≤ uh2 := by norm_num [ul2, uh2]
    have hcont : ContinuousOn quintic (Set.Icc ul2 uh2) := by
      unfold quintic
      fun_prop
    have h0 : (0 : ℝ) ∈ Set.Icc (quintic ul2) (quintic uh2) :=
      ⟨quintic_lo2.le, quintic_hi2.le⟩
    obtain ⟨u', hu', h⟩ := intermediate_value_Icc hle hcont h0
    exact ⟨u', hu', h⟩
  have h1 := bounds_of_mem uR uR_spec.1
  have hl : (1 / 2 : ℝ) < ul2 := by norm_num [ul2]
  have hh : uh2 < (7 / 10 : ℝ) := by norm_num [uh2]
  obtain ⟨w, _, hw⟩ := existsUnique_root
  have e1 := hw uR ⟨h1.1, h1.2, uR_spec.2⟩
  have e2 := hw u' ⟨by linarith [hu'.1], by linarith [hu'.2], hq⟩
  rw [e1, ← e2]
  exact hu'

theorem bR_mem2 : bR ∈ Set.Icc bl2 bh2 := by
  have hu2 := uR_mem2
  obtain ⟨b', hb', hq⟩ : ∃ b' ∈ Set.Icc bl2 bh2, Q4 b' uR = 0 := by
    have hle : bl2 ≤ bh2 := by norm_num [bl2, bh2]
    have hcont : ContinuousOn (fun b => Q4 b uR) (Set.Icc bl2 bh2) := by
      unfold Q4
      fun_prop
    have h0 : (0 : ℝ) ∈ Set.Icc (Q4 bl2 uR) (Q4 bh2 uR) :=
      ⟨(Q4_lo2 uR hu2).le, (Q4_hi2 uR hu2).le⟩
    obtain ⟨b', hb', h⟩ := intermediate_value_Icc hle hcont h0
    exact ⟨b', hb', h⟩
  have hsub : Set.Icc bl2 bh2 ⊆ Set.Icc bl bh :=
    Set.Icc_subset_Icc (by norm_num [bl, bl2]) (by norm_num [bh, bh2])
  have e := (Q4_strictMonoOn uR uR_spec.1).injOn bR_spec.1 (hsub hb')
    (by show Q4 bR uR = Q4 b' uR; rw [bR_spec.2, hq])
  rw [e]
  exact hb'
EOF
for i in 0 1 2 3 4 5 6 7 8; do
  n=${names[$i]}; m=${M[$i]}
  hu=hu; [ "$n" = bN ] && hu=_hu
  cat <<EOF

theorem close_$n (b u : ℝ) ($hu : u ∈ Set.Icc ul2 uh2) (hb : b ∈ Set.Icc bl2 bh2) :
    (225008 : ℝ) * ($m - 1e-39) ≤ $n b u ∧
      $n b u ≤ (225008 : ℝ) * ($m + 1e-39) := by
  simp only [ul2, uh2, bl2, bh2] at $hu hb
  simp only [$n]
  constructor <;> dyadic_interval [prec := 200]
EOF
done
echo
echo "end Tammes15.PaperSteps"
} > "$OUT"
echo "wrote $OUT ($(wc -l < "$OUT") lines)"
