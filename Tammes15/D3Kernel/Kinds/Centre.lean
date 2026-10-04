import Tammes15.D3Kernel.Kinds.GlueHint
import Tammes15.D3lp.TrigNat

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3lp.TrigNat Real

def nT : ℕ := 10

def sinUp (b n x : ℕ) : ℕ :=
  (sinSum b n x 0 n + x ^ (2 * n + 1) - sinSum b n x 1 n + ((2 * n + 1).factorial * 2 ^ (b * (2 * n)) - 1)) /
    ((2 * n + 1).factorial * 2 ^ (b * (2 * n)))

def sinDn (b n x : ℕ) : ℕ :=
  (sinSum b n x 0 n - (sinSum b n x 1 n + x ^ (2 * n + 1))) / ((2 * n + 1).factorial * 2 ^ (b * (2 * n)))

def cosUp (b n x : ℕ) : ℕ :=
  (cosSum b n x 0 n + x ^ (2 * n) * 2 ^ b - cosSum b n x 1 n + ((2 * n).factorial * 2 ^ (b * (2 * n)) - 1)) /
    ((2 * n).factorial * 2 ^ (b * (2 * n)))

def cosDn (b n x : ℕ) : ℕ :=
  (cosSum b n x 0 n - (cosSum b n x 1 n + x ^ (2 * n) * 2 ^ b)) / ((2 * n).factorial * 2 ^ (b * (2 * n)))

def brLoN (n K : ℕ) (a Lb : ℕ) : Bool :=
  let s := sinUp 63 n Lb
  let c := cosDn 63 n Lb
  sinLe 63 n Lb s && cosGe 63 n Lb c && decide (0 < c) && decide (s * 2 ^ K ≤ a * c) && decide (2 * Lb < cTPL)

def brHiN (n K : ℕ) (a Ub : ℕ) : Bool :=
  let s := sinDn 63 n Ub
  let c := cosUp 63 n Ub
  sinGe 63 n Ub s && cosLe 63 n Ub c && decide (a * c ≤ s * 2 ^ K) && decide (2 * Ub < cTPL)

theorem pi_gt_cTPL (x : ℕ) (h : 2 * x < cTPL) : (x : ℝ) / 2 ^ 62 < π := by
  have h1 := cTPL_le_two_pi
  have h2 : (2 * x : ℝ) < cTPL := by exact_mod_cast h
  have h3 : (0 : ℝ) < 2 ^ 62 := by positivity
  rw [div_lt_iff₀ h3]
  rw [div_le_iff₀ h3] at h1
  linarith

theorem brLoN_sound {n K a Lb : ℕ} (h : brLoN n K a Lb = true) :
    (Lb : ℝ) / 2 ^ 62 ≤ 2 * Real.arctan ((a : ℝ) / 2 ^ K) := by
  have h63 : (0 : ℝ) < 2 ^ 63 := by positivity
  have hK : (0 : ℝ) < 2 ^ K := by positivity
  have hL0 : (0 : ℝ) ≤ (Lb : ℝ) / 2 ^ 62 := by positivity
  have ht0 : (0 : ℝ) ≤ (a : ℝ) / 2 ^ K := by positivity
  have hcs : (0 : ℝ) ≤ (cosDn 63 n Lb : ℝ) := Nat.cast_nonneg _
  have has : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  simp only [brLoN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hs := sinLe_sound h1
  have hc := cosGe_sound h2
  have e : (Lb : ℝ) / 2 ^ 62 / 2 = (Lb : ℝ) / 2 ^ 63 := by ring
  have hLpi : (Lb : ℝ) / 2 ^ 62 < π := pi_gt_cTPL Lb h5
  refine lf_le_two_arctan (L := (Lb : ℝ) / 2 ^ 62) (t := (a : ℝ) / 2 ^ K) (s := (sinUp 63 n Lb : ℝ) / 2 ^ 63)
    (c := (cosDn 63 n Lb : ℝ) / 2 ^ 63) hL0 hLpi ht0 ?_ ?_ ?_ ?_
  · rw [e]; exact hs
  · rw [e]; exact hc
  · have : (0 : ℝ) < cosDn 63 n Lb := by exact_mod_cast h3
    exact div_pos this h63
  · have h4' : (sinUp 63 n Lb : ℝ) * 2 ^ K ≤ (a : ℝ) * cosDn 63 n Lb := by exact_mod_cast h4
    rw [div_mul_div_comm, div_le_div_iff₀ h63 (mul_pos hK h63)]
    have := mul_le_mul_of_nonneg_right h4' h63.le
    linarith

theorem brHiN_sound {n K a Ub : ℕ} (h : brHiN n K a Ub = true) :
    2 * Real.arctan ((a : ℝ) / 2 ^ K) ≤ (Ub : ℝ) / 2 ^ 62 := by
  have h63 : (0 : ℝ) < 2 ^ 63 := by positivity
  have hK : (0 : ℝ) < 2 ^ K := by positivity
  have hU0 : (0 : ℝ) ≤ (Ub : ℝ) / 2 ^ 62 := by positivity
  have ht0 : (0 : ℝ) ≤ (a : ℝ) / 2 ^ K := by positivity
  simp only [brHiN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hs := sinGe_sound h1
  have hc := cosLe_sound h2
  have e : (Ub : ℝ) / 2 ^ 62 / 2 = (Ub : ℝ) / 2 ^ 63 := by ring
  have hUpi : (Ub : ℝ) / 2 ^ 62 < π := pi_gt_cTPL Ub h4
  refine lf_two_arctan_le (U := (Ub : ℝ) / 2 ^ 62) (t := (a : ℝ) / 2 ^ K) (s := (sinDn 63 n Ub : ℝ) / 2 ^ 63)
    (c := (cosUp 63 n Ub : ℝ) / 2 ^ 63) hU0 hUpi ht0 ?_ ?_ ?_
  · rw [e]; exact hs
  · rw [e]; exact hc
  · have h3' : (a : ℝ) * cosUp 63 n Ub ≤ (sinDn 63 n Ub : ℝ) * 2 ^ K := by exact_mod_cast h3
    rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hK h63) h63]
    have := mul_le_mul_of_nonneg_right h3' h63.le
    linarith

def brLo (K a Lb : ℕ) : Bool := brLoN nT K a Lb

def brHi (K a Ub : ℕ) : Bool := brHiN nT K a Ub

theorem brLo_sound {K a Lb : ℕ} (h : brLo K a Lb = true) :
    (Lb : ℝ) / 2 ^ 62 ≤ 2 * Real.arctan ((a : ℝ) / 2 ^ K) := brLoN_sound h

theorem brHi_sound {K a Ub : ℕ} (h : brHi K a Ub = true) :
    2 * Real.arctan ((a : ℝ) / 2 ^ K) ≤ (Ub : ℝ) / 2 ^ 62 := brHiN_sound h

def radI (q : ℕ) (Lb Ub : ℕ) (lo hi : ℤ) : ℤ :=
  max (max (4 * (Ub : ℤ) + q * (cTPH : ℤ) - 4 * lo) (4 * hi - 4 * (Lb : ℤ) - q * (cTPL : ℤ))) 0

theorem cover_angle {K q a Lb Ub : ℕ} {lo hi : ℤ} (hL : brLo K a Lb = true) (hU : brHi K a Ub = true) :
    angR K q (a : ℤ) - (radI q Lb Ub lo hi : ℝ) / 2 ^ 64 ≤ (lo : ℝ) / 2 ^ 62 ∧
      (hi : ℝ) / 2 ^ 62 ≤ angR K q (a : ℤ) + (radI q Lb Ub lo hi : ℝ) / 2 ^ 64 := by
  have h1 := brLo_sound hL
  have h2 := brHi_sound hU
  have hpL := cTPL_le_two_pi
  have hpH := two_pi_le_cTPH
  have hr1 : ((4 * (Ub : ℤ) + q * (cTPH : ℤ) - 4 * lo : ℤ) : ℝ) ≤ radI q Lb Ub lo hi := by
    exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)
  have hr2 : ((4 * hi - 4 * (Lb : ℤ) - q * (cTPL : ℤ) : ℤ) : ℝ) ≤ radI q Lb Ub lo hi := by
    exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
  push_cast at hr1 hr2
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hA : ((a : ℤ) : ℝ) = (a : ℝ) := by push_cast; rfl
  have hX : (0 : ℝ) < 2 ^ 62 := by positivity
  have hpH' : 2 * π * 2 ^ 62 ≤ (cTPH : ℝ) := by rw [le_div_iff₀ hX] at hpH; linarith
  have hpL' : (cTPL : ℝ) ≤ 2 * π * 2 ^ 62 := by rw [div_le_iff₀ hX] at hpL; linarith
  have h1' : (Lb : ℝ) ≤ 2 * Real.arctan ((a : ℝ) / 2 ^ K) * 2 ^ 62 := by rw [div_le_iff₀ hX] at h1; linarith
  have h2' : 2 * Real.arctan ((a : ℝ) / 2 ^ K) * 2 ^ 62 ≤ (Ub : ℝ) := by rw [le_div_iff₀ hX] at h2; linarith
  have hq1 : (q : ℝ) * (2 * π * 2 ^ 62) ≤ q * cTPH := mul_le_mul_of_nonneg_left hpH' hq
  have hq2 : (q : ℝ) * cTPL ≤ q * (2 * π * 2 ^ 62) := mul_le_mul_of_nonneg_left hpL' hq
  unfold angR
  rw [hA]
  set A := 2 * Real.arctan ((a : ℝ) / 2 ^ K)
  set R := (radI q Lb Ub lo hi : ℝ)
  have e1 : (q : ℝ) * (π / 2) + A - R / 2 ^ 64 - (lo : ℝ) / 2 ^ 62 =
      ((q : ℝ) * (2 * π * 2 ^ 62) + 4 * (A * 2 ^ 62) - R - 4 * lo) / 2 ^ 64 := by field_simp; ring
  have e2 : (hi : ℝ) / 2 ^ 62 - ((q : ℝ) * (π / 2) + A + R / 2 ^ 64) =
      (4 * hi - (q : ℝ) * (2 * π * 2 ^ 62) - 4 * (A * 2 ^ 62) - R) / 2 ^ 64 := by field_simp; ring
  constructor
  · have : ((q : ℝ) * (2 * π * 2 ^ 62) + 4 * (A * 2 ^ 62) - R - 4 * lo) / 2 ^ 64 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  · have : (4 * hi - (q : ℝ) * (2 * π * 2 ^ 62) - 4 * (A * 2 ^ 62) - R) / 2 ^ 64 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith

end Tammes15.D3Kernel.Kinds
