import Tammes15.D3Kernel.Kinds.Pair

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3lp.TrigNat Tammes15.D3Kernel Tammes15.PaperSteps Real
open scoped Classical

def nW : ℕ := 16

def cosNegUp (b n x : ℕ) : ℕ :=
  (cosSum b n x 1 n + x ^ (2 * n) * 2 ^ b - cosSum b n x 0 n + ((2 * n).factorial * 2 ^ (b * (2 * n)) - 1)) /
    ((2 * n).factorial * 2 ^ (b * (2 * n)))

def cosNegDn (b n x : ℕ) : ℕ :=
  (cosSum b n x 1 n - (cosSum b n x 0 n + x ^ (2 * n) * 2 ^ b)) / ((2 * n).factorial * 2 ^ (b * (2 * n)))

def cosLoZ (x : ℕ) : ℤ :=
  if cosGe 62 nW x (cosDn 62 nW x) then (cosDn 62 nW x : ℤ) else -(cosNegUp 62 nW x : ℤ)

def cosHiZ (x : ℕ) : ℤ :=
  if (decide (0 < cosNegDn 62 nW x) && cosLeNeg 62 nW x (cosNegDn 62 nW x)) = true then -(cosNegDn 62 nW x : ℤ)
  else (cosUp 62 nW x : ℤ)

def cosLoOK (x : ℕ) (v : ℤ) : Bool := if 0 ≤ v then cosGe 62 nW x v.toNat else cosGeNeg 62 nW x (-v).toNat

def cosHiOK (x : ℕ) (v : ℤ) : Bool := if 0 ≤ v then cosLe 62 nW x v.toNat else cosLeNeg 62 nW x (-v).toNat

theorem toNat_cast_of_nonneg {v : ℤ} (hv : 0 ≤ v) : ((v.toNat : ℕ) : ℝ) = (v : ℝ) := by
  have : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg hv
  exact_mod_cast this

theorem toNat_neg_cast_of_neg {v : ℤ} (hv : ¬ 0 ≤ v) : (((-v).toNat : ℕ) : ℝ) = -(v : ℝ) := by
  have : (((-v).toNat : ℕ) : ℤ) = -v := Int.toNat_of_nonneg (by omega)
  exact_mod_cast this

theorem cosLoOK_sound {x : ℕ} {v : ℤ} (h : cosLoOK x v = true) :
    (v : ℝ) / 2 ^ 62 ≤ cos ((x : ℝ) / 2 ^ 62) := by
  unfold cosLoOK at h
  split_ifs at h with hv
  · have h1 := cosGe_sound h
    rw [toNat_cast_of_nonneg hv] at h1
    exact h1
  · have h1 := cosGeNeg_sound h
    rw [toNat_neg_cast_of_neg hv, neg_div, neg_neg] at h1
    exact h1

theorem cosHiOK_sound {x : ℕ} {v : ℤ} (h : cosHiOK x v = true) :
    cos ((x : ℝ) / 2 ^ 62) ≤ (v : ℝ) / 2 ^ 62 := by
  unfold cosHiOK at h
  split_ifs at h with hv
  · have h1 := cosLe_sound h
    rw [toNat_cast_of_nonneg hv] at h1
    exact h1
  · have h1 := cosLeNeg_sound h
    rw [toNat_neg_cast_of_neg hv, neg_div, neg_neg] at h1
    exact h1

def minpZ (a1 a2 b1 b2 : ℤ) : ℤ := min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2))

def maxpZ (a1 a2 b1 b2 : ℤ) : ℤ := max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2))

theorem fp_mul_ge_min_corner {a b A B C D : ℝ} (ha : A ≤ a) (ha' : a ≤ B) (hb : C ≤ b) (hb' : b ≤ D) :
    min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ a * b := by
  have h1 : min (A * b) (B * b) ≤ a * b := by
    by_cases hb_nonneg : 0 ≤ b
    · calc
        min (A * b) (B * b) ≤ A * b := min_le_left _ _
        _ ≤ a * b := mul_le_mul_of_nonneg_right ha hb_nonneg
    · have hb_nonpos : b ≤ 0 := by linarith
      calc
        min (A * b) (B * b) ≤ B * b := min_le_right _ _
        _ ≤ a * b := mul_le_mul_of_nonpos_right ha' hb_nonpos
  have h2 : min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ min (A * b) (B * b) := by
    have hA : min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ A * b := by
      by_cases hA_nonneg : 0 ≤ A
      · calc
          min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ A * C :=
            le_trans (min_le_left _ _) (min_le_left _ _)
          _ ≤ A * b := mul_le_mul_of_nonneg_left hb hA_nonneg
      · have hA_nonpos : A ≤ 0 := by linarith
        calc
          min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ A * D :=
            le_trans (min_le_left _ _) (min_le_right _ _)
          _ ≤ A * b := mul_le_mul_of_nonpos_left hb' hA_nonpos
    have hB : min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ B * b := by
      by_cases hB_nonneg : 0 ≤ B
      · calc
          min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ B * C :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          _ ≤ B * b := mul_le_mul_of_nonneg_left hb hB_nonneg
      · have hB_nonpos : B ≤ 0 := by linarith
        calc
          min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ B * D :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          _ ≤ B * b := mul_le_mul_of_nonpos_left hb' hB_nonpos
    exact le_min hA hB
  exact le_trans h2 h1

theorem fp_wheel_lo2 {x z w θ : ℝ} {X1 X2 Z1 Z2 W1 W2 SZ SW SZU SWU C : ℤ}
    (hx : (X1 : ℝ) / 2 ^ 62 ≤ Real.cos x ∧ Real.cos x ≤ (X2 : ℝ) / 2 ^ 62)
    (hz : (Z1 : ℝ) / 2 ^ 62 ≤ Real.cos z ∧ Real.cos z ≤ (Z2 : ℝ) / 2 ^ 62)
    (hw : (W1 : ℝ) / 2 ^ 62 ≤ Real.cos w ∧ Real.cos w ≤ (W2 : ℝ) / 2 ^ 62)
    (hsz : 0 < SZ ∧ (SZ : ℝ) / 2 ^ 62 ≤ Real.sin z) (hsw : 0 < SW ∧ (SW : ℝ) / 2 ^ 62 ≤ Real.sin w)
    (hθ : 0 ≤ θ ∧ θ ≤ Real.pi) (hc : (C : ℝ) / 2 ^ 62 ≤ Real.cos θ)
    (h1 : (X2 * 2 ^ 62 - minpZ Z1 Z2 W1 W2) * 2 ^ 62 ≤ C * SZ * SW)
    (hszu : 0 < SZU ∧ Real.sin z ≤ (SZU : ℝ) / 2 ^ 62) (hswu : 0 < SWU ∧ Real.sin w ≤ (SWU : ℝ) / 2 ^ 62)
    (h2 : (X2 * 2 ^ 62 - minpZ Z1 Z2 W1 W2) * 2 ^ 62 ≤ C * SZU * SWU) :
    θ ≤ gam x z w := by
  rcases hx with ⟨hxL, hxU⟩
  rcases hz with ⟨hzL, hzU⟩
  rcases hw with ⟨hwL, hwU⟩
  rcases hsz with ⟨hsz_pos, hszL⟩
  rcases hsw with ⟨hsw_pos, hswL⟩
  rcases hθ with ⟨hθL, hθU⟩
  have harccos_cos : Real.arccos (Real.cos θ) = θ := Real.arccos_cos hθL hθU
  set N := Real.cos x - Real.cos z * Real.cos w with hN
  set D := Real.sin z * Real.sin w with hD
  set P := (2 : ℝ) ^ 62 with hP
  have hP_pos : 0 < P := by positivity
  have hPP_pos : 0 < P * P := by positivity
  have hPP_nonneg : 0 ≤ P * P := by positivity
  have hsz_pos_real : 0 < (SZ : ℝ) := by exact_mod_cast hsz_pos
  have hsw_pos_real : 0 < (SW : ℝ) := by exact_mod_cast hsw_pos
  have hSZSW_pos : 0 < (SZ : ℝ) * (SW : ℝ) := mul_pos hsz_pos_real hsw_pos_real
  have hD_pos : 0 < D := by
    rw [hD]
    have hsinz_pos : 0 < Real.sin z := by
      have : 0 < (SZ : ℝ) / P := div_pos hsz_pos_real hP_pos
      linarith
    have hsinw_pos : 0 < Real.sin w := by
      have : 0 < (SW : ℝ) / P := div_pos hsw_pos_real hP_pos
      linarith
    exact mul_pos hsinz_pos hsinw_pos
  have hD_le_one : D ≤ 1 := by
    rw [hD]
    have hsinz_le_one : Real.sin z ≤ 1 := Real.sin_le_one _
    have hsinw_le_one : Real.sin w ≤ 1 := Real.sin_le_one _
    nlinarith
  have h_cosz_cosw_ge : (minpZ Z1 Z2 W1 W2 : ℝ) / (P * P) ≤ Real.cos z * Real.cos w := by
    have hzL' : (Z1 : ℝ) / P ≤ Real.cos z := hzL
    have hzU' : Real.cos z ≤ (Z2 : ℝ) / P := hzU
    have hwL' : (W1 : ℝ) / P ≤ Real.cos w := hwL
    have hwU' : Real.cos w ≤ (W2 : ℝ) / P := hwU
    have hmin : min (min (((Z1 : ℝ) / P) * ((W1 : ℝ) / P)) (((Z1 : ℝ) / P) * ((W2 : ℝ) / P)))
        (min (((Z2 : ℝ) / P) * ((W1 : ℝ) / P)) (((Z2 : ℝ) / P) * ((W2 : ℝ) / P))) ≤ Real.cos z * Real.cos w :=
      fp_mul_ge_min_corner hzL' hzU' hwL' hwU'
    have hmin_eq : min (min (((Z1 : ℝ) / P) * ((W1 : ℝ) / P)) (((Z1 : ℝ) / P) * ((W2 : ℝ) / P)))
        (min (((Z2 : ℝ) / P) * ((W1 : ℝ) / P)) (((Z2 : ℝ) / P) * ((W2 : ℝ) / P))) =
        (minpZ Z1 Z2 W1 W2 : ℝ) / (P * P) := by
      simp [minpZ, div_mul_div_comm, min_div_div_right hPP_nonneg, min_assoc]
    linarith
  set M := (X2 : ℝ) * P - (minpZ Z1 Z2 W1 W2 : ℝ) with hM
  have hN_le : N ≤ M / (P * P) := by
    rw [hN, hM]
    have h_cosx : Real.cos x ≤ (X2 : ℝ) / P := hxU
    nlinarith
  have hM_cases : M / (P * P) / D ≤ (C : ℝ) / P := by
    by_cases hM_nonneg : 0 ≤ M
    ·
      have hD_ge : (SZ : ℝ) * (SW : ℝ) / (P * P) ≤ D := by
        rw [hD]
        nlinarith
      have h_step1 : M / (P * P) / D ≤ M / ((SZ : ℝ) * (SW : ℝ)) := by
        have hM_nonneg_div : 0 ≤ M / (P * P) :=
          div_nonneg hM_nonneg hPP_nonneg
        have h_one_div_D_le : 1 / D ≤ (P * P) / ((SZ : ℝ) * (SW : ℝ)) := by
          field_simp [ne_of_gt hD_pos, ne_of_gt hSZSW_pos]
          nlinarith
        calc
          M / (P * P) / D = (M / (P * P)) * (1 / D) := by ring
          _ ≤ (M / (P * P)) * ((P * P) / ((SZ : ℝ) * (SW : ℝ))) :=
            mul_le_mul_of_nonneg_left h_one_div_D_le hM_nonneg_div
          _ = M / ((SZ : ℝ) * (SW : ℝ)) := by
            field_simp [ne_of_gt hSZSW_pos, ne_of_gt hPP_pos]
      have h_step2 : M / ((SZ : ℝ) * (SW : ℝ)) ≤ (C : ℝ) / P := by
        have h1_int : (X2 * 2 ^ 62 - minpZ Z1 Z2 W1 W2) * 2 ^ 62 ≤ C * SZ * SW := h1
        have h1_real : M * P ≤ (C : ℝ) * (SZ : ℝ) * (SW : ℝ) := by
          rw [hM, hP]
          exact_mod_cast h1_int
        field_simp [ne_of_gt hSZSW_pos, ne_of_gt hP_pos]
        nlinarith
      calc
        M / (P * P) / D ≤ M / ((SZ : ℝ) * (SW : ℝ)) := h_step1
        _ ≤ (C : ℝ) / P := h_step2
    ·
      have hM_neg : M < 0 := by linarith
      have hSZU : (0 : ℝ) < SZU := by exact_mod_cast hszu.1
      have hSWU : (0 : ℝ) < SWU := by exact_mod_cast hswu.1
      have hU_pos : (0 : ℝ) < (SZU : ℝ) * SWU := mul_pos hSZU hSWU
      have hz1 : Real.sin z * P ≤ SZU := by
        have := hszu.2
        rw [le_div_iff₀ hP_pos] at this
        exact this
      have hw1 : Real.sin w * P ≤ SWU := by
        have := hswu.2
        rw [le_div_iff₀ hP_pos] at this
        exact this
      have hsw0 : 0 ≤ Real.sin w * P := by
        have h' := hswL
        rw [div_le_iff₀ hP_pos] at h'
        linarith
      have hDU : D * (P * P) ≤ (SZU : ℝ) * SWU := by
        have e : D * (P * P) = (Real.sin z * P) * (Real.sin w * P) := by rw [hD]; ring
        rw [e]
        exact mul_le_mul hz1 hw1 hsw0 hSZU.le
      have h_step1 : M / (P * P) / D ≤ M / ((SZU : ℝ) * SWU) := by
        rw [div_div, div_le_div_iff₀ (by positivity) hU_pos]
        have := mul_le_mul_of_nonpos_left hDU hM_neg.le
        linarith
      have h_step2 : M / ((SZU : ℝ) * SWU) ≤ (C : ℝ) / P := by
        have h2_real : M * P ≤ (C : ℝ) * SZU * SWU := by
          rw [hM, hP]
          exact_mod_cast h2
        rw [div_le_div_iff₀ hU_pos hP_pos]
        linarith
      linarith
  have h_nd_le_cosθ : N / D ≤ Real.cos θ := by
    calc
      N / D ≤ (M / (P * P)) / D :=
        div_le_div_of_nonneg_right hN_le (by positivity)
      _ ≤ (C : ℝ) / P := hM_cases
      _ ≤ Real.cos θ := hc
  by_cases h_nd_lt_neg_one : N / D < -1
  ·
    have harccos_nd : Real.arccos (N / D) = Real.pi := Real.arccos_of_le_neg_one (by linarith)
    calc
      θ ≤ Real.pi := hθU
      _ = Real.arccos (N / D) := by symm; exact harccos_nd
      _ = gam x z w := by rfl
  ·
    have harccos_le : Real.arccos (Real.cos θ) ≤ Real.arccos (N / D) :=
      Real.arccos_le_arccos h_nd_le_cosθ
    calc
      θ = Real.arccos (Real.cos θ) := by symm; exact harccos_cos
      _ ≤ Real.arccos (N / D) := harccos_le
      _ = gam x z w := by rfl

theorem fp_wheel_hi2 {x z w θ : ℝ} {X1 X2 Z1 Z2 W1 W2 SZ SW SZU SWU C : ℤ}
    (hx : (X1 : ℝ) / 2 ^ 62 ≤ Real.cos x ∧ Real.cos x ≤ (X2 : ℝ) / 2 ^ 62)
    (hz : (Z1 : ℝ) / 2 ^ 62 ≤ Real.cos z ∧ Real.cos z ≤ (Z2 : ℝ) / 2 ^ 62)
    (hw : (W1 : ℝ) / 2 ^ 62 ≤ Real.cos w ∧ Real.cos w ≤ (W2 : ℝ) / 2 ^ 62)
    (hsz : 0 < SZ ∧ (SZ : ℝ) / 2 ^ 62 ≤ Real.sin z) (hsw : 0 < SW ∧ (SW : ℝ) / 2 ^ 62 ≤ Real.sin w)
    (hθ : 0 ≤ θ ∧ θ ≤ Real.pi) (hc : Real.cos θ ≤ (C : ℝ) / 2 ^ 62)
    (h1 : C * SZ * SW ≤ (X1 * 2 ^ 62 - maxpZ Z1 Z2 W1 W2) * 2 ^ 62)
    (hszu : 0 < SZU ∧ Real.sin z ≤ (SZU : ℝ) / 2 ^ 62) (hswu : 0 < SWU ∧ Real.sin w ≤ (SWU : ℝ) / 2 ^ 62)
    (h2 : C * SZU * SWU ≤ (X1 * 2 ^ 62 - maxpZ Z1 Z2 W1 W2) * 2 ^ 62) :
    gam x z w ≤ θ := by
  set s := (2 : ℝ) ^ 62 with hs
  have hs_pos : 0 < s := by norm_num [hs]
  have hs_sq_pos : 0 < s ^ 2 := by positivity
  rcases hx with ⟨hx_l, hx_u⟩
  rcases hz with ⟨hz_l, hz_u⟩
  rcases hw with ⟨hw_l, hw_u⟩
  rcases hsz with ⟨hsz_pos, hsz_l⟩
  rcases hsw with ⟨hsw_pos, hsw_l⟩
  rcases hθ with ⟨hθ_l, hθ_u⟩
  set N := Real.cos x - Real.cos z * Real.cos w with hN
  set D := Real.sin z * Real.sin w with hD
  have hSZ_pos_real : 0 < (SZ : ℝ) := by exact_mod_cast hsz_pos
  have hSW_pos_real : 0 < (SW : ℝ) := by exact_mod_cast hsw_pos
  have hD_pos : 0 < D := by
    have hsinz_pos : 0 < Real.sin z := by linarith
    have hsinw_pos : 0 < Real.sin w := by linarith
    positivity
  have hD_le_one : D ≤ 1 := by
    have hsinz_le_one : Real.sin z ≤ 1 := Real.sin_le_one z
    have hsinw_le_one : Real.sin w ≤ 1 := Real.sin_le_one w
    have hsinz_nonneg : 0 ≤ Real.sin z := by linarith
    have hsinw_nonneg : 0 ≤ Real.sin w := by linarith
    calc
      D = Real.sin z * Real.sin w := rfl
      _ ≤ 1 * 1 := mul_le_mul hsinz_le_one hsinw_le_one hsinw_nonneg (by norm_num)
      _ = 1 := by norm_num
  have hD_ge_SZSW_div_s_sq : (SZ * SW : ℝ) / (s ^ 2) ≤ D := by
    have hSZ_nonneg : 0 ≤ (SZ : ℝ) := by linarith
    have hSW_nonneg : 0 ≤ (SW : ℝ) := by linarith
    nlinarith

  have h_mul_le_max_corners (x y A B C D : ℝ) (hx : A ≤ x ∧ x ≤ B) (hy : C ≤ y ∧ y ≤ D) :
      x * y ≤ max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
    rcases hx with ⟨hx_l, hx_u⟩
    rcases hy with ⟨hy_l, hy_u⟩
    have h_step1 : x * y ≤ max (A * y) (B * y) := by
      by_cases hy_nonneg : 0 ≤ y
      · have hx_mul : x * y ≤ B * y := mul_le_mul_of_nonneg_right hx_u hy_nonneg
        have : B * y ≤ max (A * y) (B * y) := le_max_right _ _
        linarith
      · have hy_nonpos : y ≤ 0 := by linarith
        have hx_mul : x * y ≤ A * y := mul_le_mul_of_nonpos_right hx_l hy_nonpos
        have : A * y ≤ max (A * y) (B * y) := le_max_left _ _
        linarith
    have h_step2 : max (A * y) (B * y) ≤ max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
      have hAy : A * y ≤ max (A * C) (A * D) := by
        by_cases hA_nonneg : 0 ≤ A
        · have h : A * y ≤ A * D := mul_le_mul_of_nonneg_left hy_u hA_nonneg
          have : A * D ≤ max (A * C) (A * D) := le_max_right _ _
          linarith
        · have hA_nonpos : A ≤ 0 := by linarith
          have h : A * y ≤ A * C := mul_le_mul_of_nonpos_left hy_l hA_nonpos
          have : A * C ≤ max (A * C) (A * D) := le_max_left _ _
          linarith
      have hBy : B * y ≤ max (B * C) (B * D) := by
        by_cases hB_nonneg : 0 ≤ B
        · have h : B * y ≤ B * D := mul_le_mul_of_nonneg_left hy_u hB_nonneg
          have : B * D ≤ max (B * C) (B * D) := le_max_right _ _
          linarith
        · have hB_nonpos : B ≤ 0 := by linarith
          have h : B * y ≤ B * C := mul_le_mul_of_nonpos_left hy_l hB_nonpos
          have : B * C ≤ max (B * C) (B * D) := le_max_left _ _
          linarith
      apply max_le
      · exact le_trans hAy (le_max_left _ _)
      · exact le_trans hBy (le_max_right _ _)
    linarith

  set Az := (Z1 : ℝ) / s with hAz
  set Bz := (Z2 : ℝ) / s with hBz
  set Aw := (W1 : ℝ) / s with hAw
  set Bw := (W2 : ℝ) / s with hBw
  have h_cz_bounds : Az ≤ Real.cos z ∧ Real.cos z ≤ Bz := ⟨hz_l, hz_u⟩
  have h_cw_bounds : Aw ≤ Real.cos w ∧ Real.cos w ≤ Bw := ⟨hw_l, hw_u⟩
  have h_cz_cw_le_maxp_div_s_sq : Real.cos z * Real.cos w ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) := by
    have h_le_max : Real.cos z * Real.cos w ≤ max (max (Az * Aw) (Az * Bw)) (max (Bz * Aw) (Bz * Bw)) :=
      h_mul_le_max_corners (Real.cos z) (Real.cos w) Az Bz Aw Bw h_cz_bounds h_cw_bounds

    have h_bound_zw : Real.cos z * Real.cos w ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) := by
      have h1 : Az * Aw ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) := by
        rw [hAz, hAw]
        have h_int : (Z1 * W1 : ℤ) ≤ maxpZ Z1 Z2 W1 W2 := by
          calc
            (Z1 * W1 : ℤ) ≤ max (Z1 * W1) (Z1 * W2) := le_max_left _ _
            _ ≤ max (max (Z1 * W1) (Z1 * W2)) (max (Z2 * W1) (Z2 * W2)) := le_max_left _ _
        have h_prod : (Z1 : ℝ) * (W1 : ℝ) ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) := by exact mod_cast h_int
        calc
          ((Z1 : ℝ) / s) * ((W1 : ℝ) / s) = ((Z1 : ℝ) * (W1 : ℝ)) / (s ^ 2) := by ring
          _ ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) :=
            (div_le_div_of_nonneg_right h_prod (by positivity))
      have h2 : Az * Bw ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) := by
        rw [hAz, hBw]
        have h_int : (Z1 * W2 : ℤ) ≤ maxpZ Z1 Z2 W1 W2 := by
          calc
            (Z1 * W2 : ℤ) ≤ max (Z1 * W1) (Z1 * W2) := le_max_right _ _
            _ ≤ max (max (Z1 * W1) (Z1 * W2)) (max (Z2 * W1) (Z2 * W2)) := le_max_left _ _
        have h_prod : (Z1 : ℝ) * (W2 : ℝ) ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) := by exact mod_cast h_int
        calc
          ((Z1 : ℝ) / s) * ((W2 : ℝ) / s) = ((Z1 : ℝ) * (W2 : ℝ)) / (s ^ 2) := by ring
          _ ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) :=
            (div_le_div_of_nonneg_right h_prod (by positivity))
      have h3 : Bz * Aw ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) := by
        rw [hBz, hAw]
        have h_int : (Z2 * W1 : ℤ) ≤ maxpZ Z1 Z2 W1 W2 := by
          calc
            (Z2 * W1 : ℤ) ≤ max (Z2 * W1) (Z2 * W2) := le_max_left _ _
            _ ≤ max (max (Z1 * W1) (Z1 * W2)) (max (Z2 * W1) (Z2 * W2)) := le_max_right _ _
        have h_prod : (Z2 : ℝ) * (W1 : ℝ) ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) := by exact mod_cast h_int
        calc
          ((Z2 : ℝ) / s) * ((W1 : ℝ) / s) = ((Z2 : ℝ) * (W1 : ℝ)) / (s ^ 2) := by ring
          _ ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) :=
            (div_le_div_of_nonneg_right h_prod (by positivity))
      have h4 : Bz * Bw ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) := by
        rw [hBz, hBw]
        have h_int : (Z2 * W2 : ℤ) ≤ maxpZ Z1 Z2 W1 W2 := by
          calc
            (Z2 * W2 : ℤ) ≤ max (Z2 * W1) (Z2 * W2) := le_max_right _ _
            _ ≤ max (max (Z1 * W1) (Z1 * W2)) (max (Z2 * W1) (Z2 * W2)) := le_max_right _ _
        have h_prod : (Z2 : ℝ) * (W2 : ℝ) ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) := by exact mod_cast h_int
        calc
          ((Z2 : ℝ) / s) * ((W2 : ℝ) / s) = ((Z2 : ℝ) * (W2 : ℝ)) / (s ^ 2) := by ring
          _ ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) :=
            (div_le_div_of_nonneg_right h_prod (by positivity))

      have h_max_le : max (max (Az * Aw) (Az * Bw)) (max (Bz * Aw) (Bz * Bw)) ≤ (maxpZ Z1 Z2 W1 W2 : ℝ) / (s ^ 2) := by
        refine max_le (max_le h1 h2) (max_le h3 h4)
      linarith
    exact h_bound_zw

  set M := (X1 : ℝ) * s - (maxpZ Z1 Z2 W1 W2 : ℝ) with hM
  have hN_ge_M_div_s_sq : M / (s ^ 2) ≤ N := by
    nlinarith

  have h1_real : (C : ℝ) * (SZ : ℝ) * (SW : ℝ) ≤ M * s := by
    unfold M
    rw [hs]
    exact_mod_cast h1
  have h2_real : (C : ℝ) * (SZU : ℝ) * (SWU : ℝ) ≤ M * s := by
    unfold M
    rw [hs]
    exact_mod_cast h2

  have h_SZSW_pos : 0 < (SZ * SW : ℝ) := by positivity
  have hC_div_s_le_N_div_D : (C : ℝ) / s ≤ N / D := by
    by_cases hM_nonneg : 0 ≤ M
    ·
      have hSZU : (0 : ℝ) < SZU := by exact_mod_cast hszu.1
      have hSWU : (0 : ℝ) < SWU := by exact_mod_cast hswu.1
      have hU_pos : (0 : ℝ) < (SZU : ℝ) * SWU := mul_pos hSZU hSWU
      have hz1 : Real.sin z * s ≤ SZU := by
        have := hszu.2
        rw [le_div_iff₀ hs_pos] at this
        exact this
      have hw1 : Real.sin w * s ≤ SWU := by
        have := hswu.2
        rw [le_div_iff₀ hs_pos] at this
        exact this
      have hsz0 : 0 ≤ Real.sin z * s := by
        have : (0 : ℝ) < SZ := hSZ_pos_real
        have h' := hsz_l
        rw [div_le_iff₀ hs_pos] at h'
        linarith
      have hsw0 : 0 ≤ Real.sin w * s := by
        have : (0 : ℝ) < SW := hSW_pos_real
        have h' := hsw_l
        rw [div_le_iff₀ hs_pos] at h'
        linarith
      have hDU : D * s ^ 2 ≤ (SZU : ℝ) * SWU := by
        have e : D * s ^ 2 = (Real.sin z * s) * (Real.sin w * s) := by rw [hD]; ring
        rw [e]
        exact mul_le_mul hz1 hw1 hsw0 hSZU.le
      have hC : (C : ℝ) / s ≤ M / ((SZU : ℝ) * SWU) := by
        rw [div_le_div_iff₀ hs_pos hU_pos]
        linarith
      have hMD : M / ((SZU : ℝ) * SWU) ≤ (M / s ^ 2) / D := by
        rw [div_div, div_le_div_iff₀ hU_pos (by positivity)]
        have := mul_le_mul_of_nonneg_left hDU hM_nonneg
        linarith
      have h_M_div_s_sq_div_D_le_N_div_D : M / (s ^ 2) / D ≤ N / D :=
        (div_le_div_of_nonneg_right hN_ge_M_div_s_sq (by linarith))
      linarith
    ·
      have hM_neg : M < 0 := by linarith
      have h_ND_ge_M_div_s_sq_div_D : (M / (s ^ 2)) / D ≤ N / D :=
        (div_le_div_of_nonneg_right hN_ge_M_div_s_sq (by linarith))
      have h_sqD_ge_SZSW : (SZ * SW : ℝ) ≤ s ^ 2 * D := by

        simpa [mul_comm] using (div_le_iff₀ hs_sq_pos).mp hD_ge_SZSW_div_s_sq
      have h_M_div_s_sq_div_D_ge_M_div_SZSW : M / (SZ * SW : ℝ) ≤ (M / (s ^ 2)) / D := by
        have h_mul : M * (s ^ 2 * D) ≤ M * (SZ * SW : ℝ) :=
          mul_le_mul_of_nonpos_left h_sqD_ge_SZSW (by linarith)
        field_simp [h_SZSW_pos.ne.symm, show s ^ 2 * D ≠ 0 from by positivity]

        simpa [mul_assoc] using h_mul
      have hM_div_SZSW_ge_C_div_s : (C : ℝ) / s ≤ M / (SZ * SW : ℝ) := by
        field_simp [hs_pos.ne.symm, h_SZSW_pos.ne.symm]

        simpa [mul_comm, mul_left_comm, mul_assoc] using h1_real
      linarith

  have h_cos_theta_le_N_div_D : Real.cos θ ≤ N / D := by
    linarith
  have h_arccos_cos_theta : Real.arccos (Real.cos θ) = θ :=
    Real.arccos_cos hθ_l hθ_u
  have h_arccos_N_div_D_le_arccos_cos_theta : Real.arccos (N / D) ≤ Real.arccos (Real.cos θ) :=
    Real.arccos_le_arccos h_cos_theta_le_N_div_D
  rw [h_arccos_cos_theta] at h_arccos_N_div_D_le_arccos_cos_theta
  unfold gam
  exact h_arccos_N_div_D_le_arccos_cos_theta

theorem fp_cos_mem {lo x hi : ℝ} (h0 : 0 ≤ lo) (h1 : lo ≤ x) (h2 : x ≤ hi) (h3 : hi ≤ Real.pi) :
    Real.cos hi ≤ Real.cos x ∧ Real.cos x ≤ Real.cos lo :=
  ⟨Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) h3 h2,
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith) h1⟩

def sinHi (hi : ℕ) : ℕ := if 4 * hi < cTPL then sinUp 62 nW hi else 2 ^ 62

def sinHiOK (hi : ℕ) : Bool := if 4 * hi < cTPL then sinLe 62 nW hi (sinUp 62 nW hi) else true

theorem sinHi_sound {hi : ℕ} (h : sinHiOK hi = true) {y : ℝ} (h0 : 0 ≤ y) (hy : y ≤ (hi : ℝ) / 2 ^ 62) :
    Real.sin y ≤ (sinHi hi : ℝ) / 2 ^ 62 := by
  unfold sinHi
  unfold sinHiOK at h
  split_ifs at h ⊢ with hc
  · have hpi : ((2 * hi : ℕ) : ℝ) / 2 ^ 62 < π := pi_gt_cTPL (2 * hi) (by omega)
    push_cast at hpi
    have hhalf : (hi : ℝ) / 2 ^ 62 ≤ π / 2 := by
      have e : (2 * (hi : ℝ)) / 2 ^ 62 = 2 * ((hi : ℝ) / 2 ^ 62) := by ring
      rw [e] at hpi
      linarith
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hhalf hy
    exact hm.trans (sinLe_sound h)
  · rw [show ((2 ^ 62 : ℕ) : ℝ) / 2 ^ 62 = 1 by norm_num]
    exact Real.sin_le_one y

def wheelOK (xl xh zl zh wl wh θl θh : ℕ) : Bool :=
  let X1 := cosLoZ xh
  let X2 := cosHiZ xl
  let Z1 := cosLoZ zh
  let Z2 := cosHiZ zl
  let W1 := cosLoZ wh
  let W2 := cosHiZ wl
  let SZ := min (sinDn 62 nW zl) (sinDn 62 nW zh)
  let SW := min (sinDn 62 nW wl) (sinDn 62 nW wh)
  let CL := cosLoZ θl
  let CH := cosHiZ θh
  cosLoOK xh X1 && cosHiOK xl X2 && cosLoOK zh Z1 && cosHiOK zl Z2 && cosLoOK wh W1 && cosHiOK wl W2 &&
    sinGe 62 nW zl SZ && sinGe 62 nW zh SZ && sinGe 62 nW wl SW && sinGe 62 nW wh SW && decide (0 < SZ) &&
    decide (0 < SW) && cosLoOK θl CL && cosHiOK θh CH && decide (2 * xh < cTPL) && decide (2 * zh < cTPL) &&
    decide (2 * wh < cTPL) && decide (2 * θl < cTPL) && decide (2 * θh < cTPL) &&
    decide ((X2 * 2 ^ 62 - minpZ Z1 Z2 W1 W2) * 2 ^ 62 ≤ CL * SZ * SW) &&
    decide ((X2 * 2 ^ 62 - minpZ Z1 Z2 W1 W2) * 2 ^ 62 ≤ CL * (sinHi zh : ℤ) * (sinHi wh : ℤ)) &&
    decide (CH * SZ * SW ≤ (X1 * 2 ^ 62 - maxpZ Z1 Z2 W1 W2) * 2 ^ 62) &&
    sinHiOK zh && sinHiOK wh && decide (0 < sinHi zh) && decide (0 < sinHi wh) &&
    decide (CH * (sinHi zh : ℤ) * (sinHi wh : ℤ) ≤ (X1 * 2 ^ 62 - maxpZ Z1 Z2 W1 W2) * 2 ^ 62)

theorem sin_lb {lo hi S : ℕ} {y : ℝ} (hlo : sinGe 62 nW lo S = true) (hhi : sinGe 62 nW hi S = true)
    (h1 : (lo : ℝ) / 2 ^ 62 ≤ y) (h2 : y ≤ (hi : ℝ) / 2 ^ 62) (hpi : 2 * hi < cTPL) :
    (S : ℝ) / 2 ^ 62 ≤ Real.sin y := by
  have a := sinGe_sound hlo
  have b := sinGe_sound hhi
  have hm := lf_sin_ge_min (a := (lo : ℝ) / 2 ^ 62) (b := (hi : ℝ) / 2 ^ 62) (x := y)
    (div_nonneg (Nat.cast_nonneg _) (by norm_num)) h1 h2 (pi_gt_cTPL hi hpi).le
  exact le_trans (le_min a b) hm

theorem wheelOK_sound {xl xh zl zh wl wh θl θh : ℕ} (h : wheelOK xl xh zl zh wl wh θl θh = true) {x z w : ℝ}
    (hx : (xl : ℝ) / 2 ^ 62 ≤ x ∧ x ≤ (xh : ℝ) / 2 ^ 62) (hz : (zl : ℝ) / 2 ^ 62 ≤ z ∧ z ≤ (zh : ℝ) / 2 ^ 62)
    (hw : (wl : ℝ) / 2 ^ 62 ≤ w ∧ w ≤ (wh : ℝ) / 2 ^ 62) :
    (θl : ℝ) / 2 ^ 62 ≤ gam x z w ∧ gam x z w ≤ (θh : ℝ) / 2 ^ 62 := by
  simp only [wheelOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hX1, hX2⟩, hZ1⟩, hZ2⟩, hW1⟩, hW2⟩, hsz1⟩, hsz2⟩, hsw1⟩, hsw2⟩, hSZ⟩, hSW⟩,
    hCL⟩, hCH⟩, hxpi⟩, hzpi⟩, hwpi⟩, hlpi⟩, hhpi⟩, h1⟩, h2⟩, h3⟩, hzu⟩, hwu⟩, hzu0⟩, hwu0⟩, h4⟩ := h
  have h0 : ∀ a : ℕ, (0 : ℝ) ≤ (a : ℝ) / 2 ^ 62 := fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have cx := fp_cos_mem (h0 xl) hx.1 hx.2 (pi_gt_cTPL xh hxpi).le
  have cz := fp_cos_mem (h0 zl) hz.1 hz.2 (pi_gt_cTPL zh hzpi).le
  have cw := fp_cos_mem (h0 wl) hw.1 hw.2 (pi_gt_cTPL wh hwpi).le
  have bx : ((cosLoZ xh : ℤ) : ℝ) / 2 ^ 62 ≤ Real.cos x ∧ Real.cos x ≤ ((cosHiZ xl : ℤ) : ℝ) / 2 ^ 62 :=
    ⟨le_trans (cosLoOK_sound hX1) cx.1, le_trans cx.2 (cosHiOK_sound hX2)⟩
  have bz : ((cosLoZ zh : ℤ) : ℝ) / 2 ^ 62 ≤ Real.cos z ∧ Real.cos z ≤ ((cosHiZ zl : ℤ) : ℝ) / 2 ^ 62 :=
    ⟨le_trans (cosLoOK_sound hZ1) cz.1, le_trans cz.2 (cosHiOK_sound hZ2)⟩
  have bw : ((cosLoZ wh : ℤ) : ℝ) / 2 ^ 62 ≤ Real.cos w ∧ Real.cos w ≤ ((cosHiZ wl : ℤ) : ℝ) / 2 ^ 62 :=
    ⟨le_trans (cosLoOK_sound hW1) cw.1, le_trans cw.2 (cosHiOK_sound hW2)⟩
  have sz := sin_lb hsz1 hsz2 hz.1 hz.2 hzpi
  have sw := sin_lb hsw1 hsw2 hw.1 hw.2 hwpi
  have sz' : (0 : ℤ) < ((min (sinDn 62 nW zl) (sinDn 62 nW zh) : ℕ) : ℤ) ∧
      (((min (sinDn 62 nW zl) (sinDn 62 nW zh) : ℕ) : ℤ) : ℝ) / 2 ^ 62 ≤ Real.sin z :=
    ⟨by exact_mod_cast hSZ, by rw [Int.cast_natCast]; exact sz⟩
  have sw' : (0 : ℤ) < ((min (sinDn 62 nW wl) (sinDn 62 nW wh) : ℕ) : ℤ) ∧
      (((min (sinDn 62 nW wl) (sinDn 62 nW wh) : ℕ) : ℤ) : ℝ) / 2 ^ 62 ≤ Real.sin w :=
    ⟨by exact_mod_cast hSW, by rw [Int.cast_natCast]; exact sw⟩
  have tl : 0 ≤ (θl : ℝ) / 2 ^ 62 ∧ (θl : ℝ) / 2 ^ 62 ≤ π := ⟨h0 θl, (pi_gt_cTPL θl hlpi).le⟩
  have th : 0 ≤ (θh : ℝ) / 2 ^ 62 ∧ (θh : ℝ) / 2 ^ 62 ≤ π := ⟨h0 θh, (pi_gt_cTPL θh hhpi).le⟩
  have zu : (0 : ℤ) < ((sinHi zh : ℕ) : ℤ) ∧ Real.sin z ≤ (((sinHi zh : ℕ) : ℤ) : ℝ) / 2 ^ 62 :=
    ⟨by exact_mod_cast hzu0, by rw [Int.cast_natCast]; exact sinHi_sound hzu ((h0 zl).trans hz.1) hz.2⟩
  have wu : (0 : ℤ) < ((sinHi wh : ℕ) : ℤ) ∧ Real.sin w ≤ (((sinHi wh : ℕ) : ℤ) : ℝ) / 2 ^ 62 :=
    ⟨by exact_mod_cast hwu0, by rw [Int.cast_natCast]; exact sinHi_sound hwu ((h0 wl).trans hw.1) hw.2⟩
  exact ⟨fp_wheel_lo2 bx bz bw sz' sw' tl (cosLoOK_sound hCL) h1 zu wu h2,
    fp_wheel_hi2 bx bz bw sz' sw' th (cosHiOK_sound hCH) h3 zu wu h4⟩

section Free

variable {g : ℕ}

theorem faceIter_lab (s : Sol g) (e : s.P.G.Dart) : ∀ j : ℕ,
    ((Ctx.code g).faceAt)^[j] ((s.lab e : Fin (Ctx.D g)) : ℕ) = ((s.lab ((s.P.R.face ^ j) e) : Fin (Ctx.D g)) : ℕ)
  | 0 => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply', faceIter_lab s e j, pow_succ', Equiv.Perm.mul_apply]
    exact s.hm.face _

theorem fin6_sub_one (i : Fin 6) : ((i - 1 : Fin 6) : ℕ) = ((i : ℕ) + 5) % 6 := by
  fin_cases i <;> rfl

def fcB (lh m : ℕ) : ℕ := lhB lh (35 + m) % 6

def fdI (g lh m : ℕ) : ℕ := ((Ctx.code g).faceAt)^[fcB lh m] (Ctx.base g m)

def fbI (g lh m : ℕ) : ℕ := revC (Ctx.code g) (((Ctx.code g).faceAt)^[(fcB lh m + 5) % 6] (Ctx.base g m))

theorem lab_freeDart (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) (lh : ℕ) (m : Fin (Ctx.k g)) :
    ((s.lab (freeDart s.H (glueOf s hn hD lh) m) : Fin (Ctx.D g)) : ℕ) = fdI g lh m := by
  unfold freeDart fdI
  rw [← faceIter_lab, s.hH m]
  rfl

theorem lab_freeBack (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) (lh : ℕ) (m : Fin (Ctx.k g)) :
    ((s.lab (freeBack s.H (glueOf s hn hD lh) m) : Fin (Ctx.D g)) : ℕ) = fbI g lh m := by
  unfold freeBack fbI
  rw [← revC_sol, ← faceIter_lab, s.hH m, fin6_sub_one]
  rfl

theorem freeDart_fst (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) (lh : ℕ) (m : Fin (Ctx.k g)) :
    (((freeDart s.H (glueOf s hn hD lh) m).fst : Fin s.P.n) : ℕ) = (Ctx.code g).fstAt (fdI g lh m) := by
  rw [← lab_freeDart s hn hD lh m]
  exact (s.hm.fst _).symm

end Free

def rKey (hv m j : ℕ) : ℕ := hvB hv (258 + (6 * m + j))

def rLoK (box hv m j : ℕ) : ℕ := bnd box (2 * rKey hv m j)

def rHiK (box hv m j : ℕ) : ℕ := bnd box (2 * rKey hv m j + 1)

def fRef (g lh m : ℕ) : ℕ := refI (Ctx.code g) lh ((Ctx.code g).fstAt (fdI g lh m))

def fqLo (g box hv n lh m : ℕ) : ℤ := turnLoZ box hv (Ctx.code g) n (fRef g lh m) (fbI g lh m) + lhW lh (100 + 2 * m)

def fqHi (g box hv n lh m : ℕ) : ℤ := turnHiZ box hv (Ctx.code g) n (fRef g lh m) (fbI g lh m) + lhW lh (101 + 2 * m)

def qrI (g box hv n lh m : ℕ) : ℤ := radA lh (17 + m) (fqLo g box hv n lh m) (fqHi g box hv n lh m)

def rrI (box hv lh m : ℕ) : ℤ :=
  radA lh (21 + m) (kfix (rLoK box hv m (fcB lh m))) (kfix (rHiK box hv m (fcB lh m)))

def freeOK (g box hv n lh m : ℕ) : Bool :=
  kgood (rLoK box hv m (fcB lh m)) && kgood (rHiK box hv m (fcB lh m)) &&
    kgood (rLoK box hv m ((fcB lh m + 5) % 6)) && kgood (rHiK box hv m ((fcB lh m + 5) % 6)) &&
    cenOK lh (17 + m) && cenOK lh (21 + m) &&
    goodAll box hv (tf (Ctx.code g) n (fRef g lh m)) (degC (Ctx.code g) (fRef g lh m)) &&
    wheelOK (kfix (rLoK box hv m ((fcB lh m + 5) % 6))) (kfix (rHiK box hv m ((fcB lh m + 5) % 6)))
      (kfix (rLoK box hv m (fcB lh m))) (kfix (rHiK box hv m (fcB lh m))) (kfix (dKey box hv)) (kfix (dKeyH box hv))
      (lhW lh (100 + 2 * m)) (lhW lh (101 + 2 * m))

section Encl

variable {g : ℕ}

noncomputable def enclF (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) (box hv lh n : ℕ) :
    Encl s.P (Ctx.k g) where
  dc := cen lh 0
  dr := (drI box hv lh : ℝ) / 2 ^ 64
  pc v := cen lh (1 + v)
  pr v := (prI box hv (Ctx.code g) n lh v : ℝ) / 2 ^ 64
  qc m := cen lh (17 + m)
  qr m := (qrI g box hv n lh m : ℝ) / 2 ^ 64
  rc m := cen lh (21 + m)
  rr m := (rrI box hv lh m : ℝ) / 2 ^ 64

theorem freeCover (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) {box hv lh n : ℕ} (hn' : s.P.n = n)
    (hr : lhB lh 1 < s.P.n) (h2 : lhB lh 2 < Ctx.D g)
    (hpar : ∀ v : Fin s.P.n, v ≠ (glueOf s hn hD lh).root → lhB lh (3 + v) < Ctx.D g)
    (hper : ∀ i < Ctx.D g, 0 < (Ctx.code g).period i)
    (hk1 : kgood (dKey box hv) = true) (hk2 : kgood (dKeyH box hv) = true)
    (hB : (walkBox box (vmOf s hv)).Mem (PVar.val s.A))
    (m : Fin (Ctx.k g)) (hf : freeOK g box hv n lh m = true) :
    (∃ β : ℝ × ℝ,
      procsW.wheel s.P (Ctx.k g) (walkBox box (vmOf s hv)) m ((glueOf s hn hD lh).freeCorner m) = some β ∧
      (enclF s hn hD box hv lh n).qc m - (enclF s hn hD box hv lh n).qr m ≤
        turnLo (walkBox box (vmOf s hv)) ((glueOf s hn hD lh).refD (freeDart s.H (glueOf s hn hD lh) m).fst)
          (freeBack s.H (glueOf s hn hD lh) m) + β.1 ∧
      turnHi (walkBox box (vmOf s hv)) ((glueOf s hn hD lh).refD (freeDart s.H (glueOf s hn hD lh) m).fst)
          (freeBack s.H (glueOf s hn hD lh) m) + β.2 ≤
        (enclF s hn hD box hv lh n).qc m + (enclF s hn hD box hv lh n).qr m) ∧
    ((enclF s hn hD box hv lh n).rc m - (enclF s hn hD box hv lh n).rr m ≤
        (walkBox box (vmOf s hv)).lo (.r m ((glueOf s hn hD lh).freeCorner m)) ∧
      (walkBox box (vmOf s hv)).hi (.r m ((glueOf s hn hD lh).freeCorner m)) ≤
        (enclF s hn hD box hv lh n).rc m + (enclF s hn hD box hv lh n).rr m) := by
  simp only [freeOK, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hz1, hz2⟩, hx1⟩, hx2⟩, hcq⟩, hcr⟩, hgood⟩, hwh⟩ := hf
  set gl := glueOf s hn hD lh with hgl
  set B := walkBox box (vmOf s hv) with hBdef
  have hfc : ((gl.freeCorner m : Fin 6) : ℕ) = fcB lh m := rfl
  have hfp : ((gl.freeCorner m - 1 : Fin 6) : ℕ) = (fcB lh m + 5) % 6 := by rw [fin6_sub_one, hfc]
  have ezl : B.lo (.r m (gl.freeCorner m)) = (kfix (rLoK box hv m (fcB lh m)) : ℝ) / 2 ^ 62 := by
    rw [← keyVal_kgood hz1]
    show keyVal (bnd box (2 * hvB hv (258 + (6 * (m : ℕ) + ((gl.freeCorner m : Fin 6) : ℕ))))) = _
    rw [hfc]
    rfl
  have ezh : B.hi (.r m (gl.freeCorner m)) = (kfix (rHiK box hv m (fcB lh m)) : ℝ) / 2 ^ 62 := by
    rw [← keyVal_kgood hz2]
    show keyVal (bnd box (2 * hvB hv (258 + (6 * (m : ℕ) + ((gl.freeCorner m : Fin 6) : ℕ))) + 1)) = _
    rw [hfc]
    rfl
  have exl : B.lo (.r m (gl.freeCorner m - 1)) = (kfix (rLoK box hv m ((fcB lh m + 5) % 6)) : ℝ) / 2 ^ 62 := by
    rw [← keyVal_kgood hx1]
    show keyVal (bnd box (2 * hvB hv (258 + (6 * (m : ℕ) + ((gl.freeCorner m - 1 : Fin 6) : ℕ))))) = _
    rw [hfp]
    rfl
  have exh : B.hi (.r m (gl.freeCorner m - 1)) = (kfix (rHiK box hv m ((fcB lh m + 5) % 6)) : ℝ) / 2 ^ 62 := by
    rw [← keyVal_kgood hx2]
    show keyVal (bnd box (2 * hvB hv (258 + (6 * (m : ℕ) + ((gl.freeCorner m - 1 : Fin 6) : ℕ))) + 1)) = _
    rw [hfp]
    rfl
  have ewl : B.lo .d = (kfix (dKey box hv) : ℝ) / 2 ^ 62 := keyVal_kgood hk1
  have ewh : B.hi .d = (kfix (dKeyH box hv) : ℝ) / 2 ^ 62 := keyVal_kgood hk2

  have hwb : ∀ y ∈ wheelSet B m (gl.freeCorner m),
      (lhW lh (100 + 2 * m) : ℝ) / 2 ^ 62 ≤ y ∧ y ≤ (lhW lh (101 + 2 * m) : ℝ) / 2 ^ 62 := by
    rintro y ⟨x, z, w, hx, hz, hw, rfl⟩
    rw [exl, exh] at hx
    rw [ezl, ezh] at hz
    rw [ewl, ewh] at hw
    exact wheelOK_sound hwh hx hz hw
  have hne : (wheelSet B m (gl.freeCorner m)).Nonempty :=
    ⟨_, _, _, _, hB (.r m (gl.freeCorner m - 1)), hB (.r m (gl.freeCorner m)), hB .d, rfl⟩
  have hinf := le_sInf_wheelSet hne (fun y hy => (hwb y hy).1)
  have hsup := sSup_wheelSet_le hne (fun y hy => (hwb y hy).2)

  have hfst := freeDart_fst s hn hD lh m
  have hlabA : ((s.lab (gl.refD (freeDart s.H gl m).fst) : Fin (Ctx.D g)) : ℕ) = fRef g lh m := by
    rw [lab_refD s hn hD hr h2 hpar, hfst]
    rfl
  have hlabB : ((s.lab (freeBack s.H gl m) : Fin (Ctx.D g)) : ℕ) = fbI g lh m := lab_freeBack s hn hD lh m
  have hgood' : goodAll box hv (tf (Ctx.code g) s.P.n ((s.lab (gl.refD (freeDart s.H gl m).fst) : Fin (Ctx.D g)) : ℕ))
      (degC (Ctx.code g) ((s.lab (gl.refD (freeDart s.H gl m).fst) : Fin (Ctx.D g)) : ℕ)) = true := by
    have hgood2 := hgood
    rw [← hn'] at hgood2
    rw [hlabA]
    exact hgood2
  have t1 := turnLo_ge s hper (gl.refD (freeDart s.H gl m).fst) (freeBack s.H gl m) hgood'
  have t2 := turnHi_le s hper (gl.refD (freeDart s.H gl m).fst) (freeBack s.H gl m) hgood'
  have e1 : turnLoZ box hv (Ctx.code g) s.P.n (fRef g lh m) (fbI g lh m) =
      turnLoZ box hv (Ctx.code g) n (fRef g lh m) (fbI g lh m) :=
    congrArg (fun k => turnLoZ box hv (Ctx.code g) k (fRef g lh m) (fbI g lh m)) hn'
  have e2 : turnHiZ box hv (Ctx.code g) s.P.n (fRef g lh m) (fbI g lh m) =
      turnHiZ box hv (Ctx.code g) n (fRef g lh m) (fbI g lh m) :=
    congrArg (fun k => turnHiZ box hv (Ctx.code g) k (fRef g lh m) (fbI g lh m)) hn'
  rw [hlabA, hlabB, e1] at t1
  rw [hlabA, hlabB, e2] at t2
  have hq := cover_cen (lo := fqLo g box hv n lh m) (hi := fqHi g box hv n lh m) hcq
  have hrr := cover_cen (lo := (kfix (rLoK box hv m (fcB lh m)) : ℤ)) (hi := (kfix (rHiK box hv m (fcB lh m)) : ℤ))
    hcr
  have eLo : ((fqLo g box hv n lh m : ℤ) : ℝ) / 2 ^ 62 =
      (turnLoZ box hv (Ctx.code g) n (fRef g lh m) (fbI g lh m) : ℝ) / 2 ^ 62 + (lhW lh (100 + 2 * m) : ℝ) / 2 ^ 62 := by
    unfold fqLo
    push_cast
    ring
  have eHi : ((fqHi g box hv n lh m : ℤ) : ℝ) / 2 ^ 62 =
      (turnHiZ box hv (Ctx.code g) n (fRef g lh m) (fbI g lh m) : ℝ) / 2 ^ 62 + (lhW lh (101 + 2 * m) : ℝ) / 2 ^ 62 := by
    unfold fqHi
    push_cast
    ring
  refine ⟨⟨(sInf (wheelSet B m (gl.freeCorner m)), sSup (wheelSet B m (gl.freeCorner m))), rfl, ?_, ?_⟩, ?_, ?_⟩
  · show cen lh (17 + m) - (qrI g box hv n lh m : ℝ) / 2 ^ 64 ≤ _
    have := hq.1
    rw [eLo] at this
    unfold qrI
    linarith
  · show _ ≤ cen lh (17 + m) + (qrI g box hv n lh m : ℝ) / 2 ^ 64
    have := hq.2
    rw [eHi] at this
    unfold qrI
    linarith
  · show cen lh (21 + m) - (rrI box hv lh m : ℝ) / 2 ^ 64 ≤ _
    rw [ezl]
    have := hrr.1
    push_cast at this
    exact this
  · show _ ≤ cen lh (21 + m) + (rrI box hv lh m : ℝ) / 2 ^ 64
    rw [ezh]
    have := hrr.2
    push_cast at this
    exact this

end Encl

end Tammes15.D3Kernel.Kinds
