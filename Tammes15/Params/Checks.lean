import Tammes15.Params.Generic
import Tammes15.Numerics.HexData
import Tammes15.Params.Pi

/-!
# The inequalities on the parameters

Inequalities on the constants and the parameters of the program, one statement each. The rational
witnesses of the proofs are those that code/lean-data/witness.gp prints and checks in exact arithmetic (witness.out).

1. The constants of data/params15ft.txt, read as exact decimals, are outward
   enclosures: `dlo_file ≤ dlo`, `dhi ≤ dhi_file`, `alo_file ≤ α(dlo)`, `α(dhi) ≤ ahi_file`,
   `smax(dhi) ≤ shi_file`.
2. The range: `53.65785° < ψ*` is `dlo_lt_arccos_root` (Hyps/Interfaces.lean); `ψ* < 53.6578502°`
   is `arccos_root_lt` below.
3. `56.6716°` lies above the Fejes Tóth value `arccos ((cot² ω - 1) / 2)`, `ω = 15π / (6 · 13)`.
4. The margins of Section 4.3 of the paper are proved elsewhere: `two_pi_lt_seven_dlo`, `alpha_dhi_lt` and
   `margin_perims` in Trigrows/Margins.lean, `onehex_chord_margin` in Rattlers/HexChord.lean and
   `margin_onehex_poly` in Rattlers/HexPoly.lean.
-/

open Real

namespace Tammes15.Params

theorem dlo_file_le : (0.93650615204123937289 : ℝ) ≤ dlo := by
  unfold dlo
  have hpi : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  nlinarith

theorem dhi_le_file : dhi ≤ (0.98910601237321848052 : ℝ) := by
  unfold dhi
  have hpi := Real.pi_lt_d20
  have hcalc : 566716 / 10000 * (π / 180) = (141679 / 450000) * π := by ring
  rw [hcalc]
  have hpos : 0 < (141679 : ℝ) / 450000 := by norm_num
  have h_mul : (141679 / 450000) * π < (141679 / 450000) * 3.14159265358979323847 :=
    mul_lt_mul_of_pos_left hpi hpos
  have hbound : (141679 / 450000) * 3.14159265358979323847 ≤ (0.98910601237321848052 : ℝ) := by
    norm_num
  linarith

theorem alo_file_le : (1.18952772983819258225 : ℝ) ≤ alpha dlo := by
  set a := (1.18952772983819258225 : ℝ) with ha
  set cU := (7407573809396648601759619947 / 12500000000000000000000000000 : ℝ) with hcU
  have ha0 : 0 ≤ a := by
    unfold a; norm_num
  have haπ : a ≤ π := by
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    unfold a; nlinarith
  have hcos_dlo_pos : 0 < cos dlo := by
    have hdlo_pos : 0 < dlo := by
      unfold dlo; nlinarith [Real.pi_pos]
    have hdlo_lt_pi_div_two : dlo < π / 2 := by
      unfold dlo; nlinarith [Real.pi_pos]
    have h_neg : -(π / 2) < dlo := by
      linarith
    exact Real.cos_pos_of_mem_Ioo ⟨h_neg, hdlo_lt_pi_div_two⟩
  have hcos_dlo_le_cU : cos dlo ≤ cU := by
    have hdlo_eq : dlo = (5365785 / 18000000) * π := by
      unfold dlo; ring
    rw [hdlo_eq]
    refine Tammes15.Numerics.cos_mul_pi_le 13 (p := 3.14159265358979323846) ?_ ?_ ?_ ?_ ?_
    · norm_num
    · exact Real.pi_gt_d20.le
    · norm_num
    · norm_num
    · unfold Tammes15.Numerics.cosT
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
  have h_cU_div : cU / (1 + cU) ≤ cos a := by
    refine Tammes15.Numerics.le_cos_of_cosT 13 ha0 ?_
    unfold Tammes15.Numerics.cosT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  exact Tammes15.Params.le_alpha_of hcos_dlo_pos hcos_dlo_le_cU ha0 haπ h_cU_div

theorem alpha_dhi_le_file : alpha dhi ≤ (1.20830549335659207180 : ℝ) := by
  set a := (1.20830549335659207180 : ℝ) with ha
  set cL := (274718519051154318642656362663 / 500000000000000000000000000000 : ℝ) with hcL
  have ha0 : 0 ≤ a := by
    unfold a; norm_num
  have haπ : a ≤ π := by
    unfold a; have h := Real.pi_gt_three; nlinarith
  have hcL_pos : 0 < cL := by
    unfold cL; norm_num
  have h_dhi_eq : dhi = (141679 / 450000 : ℝ) * π := by
    unfold dhi; ring
  have h_cL_le_cos_dhi : cL ≤ cos dhi := by
    rw [h_dhi_eq]
    have hp : π ≤ (3.14159265358979323847 : ℝ) := by
      have h := Tammes15.Params.pi_lt_d21; linarith
    have hq0 : 0 ≤ (141679 / 450000 : ℝ) := by norm_num
    have hqp : (141679 / 450000 : ℝ) * (3.14159265358979323847 : ℝ) ≤ 3 := by norm_num
    have h_taylor : cL ≤ Tammes15.Numerics.cosT 13 ((141679 / 450000 : ℝ) * (3.14159265358979323847 : ℝ)) -
        ((141679 / 450000 : ℝ) * (3.14159265358979323847 : ℝ)) ^ (2 * 13) / ((2 * 13).factorial : ℝ) := by
      unfold cL Tammes15.Numerics.cosT
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    exact Tammes15.Numerics.le_cos_mul_pi 13 hp hq0 hqp h_taylor
  have h_cos_a_le : cos a ≤ cL / (1 + cL) := by
    have h_taylor : Tammes15.Numerics.cosT 13 a + a ^ (2 * 13) / ((2 * 13).factorial : ℝ) ≤ cL / (1 + cL) := by
      unfold cL Tammes15.Numerics.cosT a
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    have ha0' : 0 ≤ a := ha0
    exact Tammes15.Numerics.cos_le_of_cosT 13 ha0' h_taylor
  exact Tammes15.Params.alpha_le_of hcL_pos h_cL_le_cos_dhi ha0 haπ h_cos_a_le

theorem smax_dhi_le_file : smax dhi ≤ (3.73170040409990243346 : ℝ) := by
  set s := (3.73170040409990243346 : ℝ) / 4 with hs_def
  have hs_eq : (3.73170040409990243346 : ℝ) = 4 * s := by
    rw [hs_def]
    norm_num
  rw [hs_eq]
  set cL := (549437038102308637287154157469 : ℝ) / 1000000000000000000000000000000 with hcL_def
  set Cu := (119097321744770593743834413187 : ℝ) / 200000000000000000000000000000 with hCu_def
  set Sl := (803365233770148182287774520697 : ℝ) / 1000000000000000000000000000000 with hSl_def
  have hcL_pos : 0 < cL := by rw [hcL_def]; norm_num
  have hs_pos : 0 < s := by rw [hs_def]; norm_num
  have hSl_pos : 0 < Sl := by rw [hSl_def]; norm_num
  refine smax_le_of (d := dhi) (s := s) (cL := cL) (Cu := Cu) (Sl := Sl) hcL_pos ?_ hs_pos ?_ ?_ ?_ hSl_pos ?_
  · -- cL ≤ cos dhi
    have hdhi : dhi = (141679/450000 : ℝ) * π := by
      dsimp [dhi]
      ring
    rw [hdhi]
    refine Tammes15.Numerics.le_cos_mul_pi 13 (p := 3.141592653589793238463) (by exact Tammes15.Params.pi_lt_d21.le) (by norm_num) (by norm_num) ?_
    rw [hcL_def]
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · -- s < π / 2
    rw [hs_def]
    have h : (3.73170040409990243346 : ℝ) < 2 * π := by
      have h6 : (3.73170040409990243346 : ℝ) < 6 := by norm_num
      have hpi : 3 < π := Real.pi_gt_three
      nlinarith
    nlinarith
  · -- cos s ≤ Cu
    refine Tammes15.Numerics.cos_le_of_cosT 13 (by rw [hs_def]; norm_num) ?_
    rw [hCu_def, hs_def]
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · -- Sl ≤ sin s
    refine Tammes15.Numerics.le_sin_of_sinT 13 (by rw [hs_def]; norm_num) ?_
    rw [hSl_def, hs_def]
    simp only [Tammes15.Numerics.sinT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · -- Cu ^ 2 ≤ cL * Sl ^ 2
    rw [hcL_def, hCu_def, hSl_def]
    norm_num

theorem arccos_root_lt (u : ℝ) (h1 : 1 / 2 < u) (h2 : u < 7 / 10) (h0 : quintic u = 0) :
    arccos u < 536578502 / 10000000 * (π / 180) := by
  set b := 536578502 / 10000000 * (π / 180) with hb
  let cU : ℝ := 592605901940033/1000000000000000
  have hb_nonneg : 0 ≤ b := by
    rw [hb]
    positivity
  have hb_le_pi : b ≤ π := by
    rw [hb]
    have h : 536578502 / 10000000 / 180 ≤ 1 := by norm_num
    nlinarith [Real.pi_pos]
  have hu_le_one : u ≤ 1 := by linarith
  have h_cosb_le_cU : cos b ≤ cU := by
    rw [hb]
    have hp : (3.14159265358979323846 : ℝ) ≤ π := Real.pi_gt_d20.le
    have hp0 : 0 ≤ (3.14159265358979323846 : ℝ) := by norm_num
    have hq0 : 0 ≤ (536578502 / 10000000 / 180 : ℝ) := by norm_num
    have hq1 : (536578502 / 10000000 / 180 : ℝ) ≤ 1 := by norm_num
    have h := Tammes15.Numerics.cos_mul_pi_le (c := cU) 10 (p := 3.14159265358979323846) hp0 hp hq0 hq1 ?_
    · -- h : cos ((536578502 / 10000000 / 180) * π) ≤ cU
      -- we need: cos (536578502 / 10000000 * (π / 180)) ≤ cU
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_inv_mul] using h
    · simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
  have h_quintic_cU_neg : quintic cU < 0 := by
    unfold quintic
    norm_num
  have h_cU_ge_half : (1/2 : ℝ) ≤ cU := by
    unfold cU
    norm_num
  have h_cU_le_seven_tenths : cU ≤ 7/10 := by
    unfold cU
    norm_num
  have h_cU_lt_u : cU < u :=
    Tammes15.Params.lt_of_quintic_neg h1 h2 h_cU_ge_half h_cU_le_seven_tenths h0 h_quintic_cU_neg
  have h_cosb_lt_u : cos b < u := by
    linarith
  exact Tammes15.Numerics.arccos_lt_of_cos_lt hb_nonneg hb_le_pi hu_le_one h_cosb_lt_u

theorem fejesToth_value_lt_dhi : arccos ((cot (15 * π / (6 * 13)) ^ 2 - 1) / 2) < dhi := by
  refine ft_lt_of (d := dhi) (SU := 568064746733/1000000000000) (cU := 274718519063/500000000000) ?hd0 ?hdπ ?hS ?hc ?h
  · -- 0 < dhi
    unfold dhi
    have hπ := Real.pi_pos
    positivity
  · -- dhi ≤ π
    unfold dhi
    have hπ := Real.pi_pos
    nlinarith
  · -- sin (15 * π / (6 * 13)) ≤ SU
    have h : 15 * π / (6 * 13) = (5/26) * π := by ring
    rw [h]
    have hπ_le : π ≤ 3.1415926536 := by linarith [Real.pi_lt_d20]
    refine Tammes15.Numerics.sin_mul_pi_le 10 (p := 3.1415926536) hπ_le (by norm_num) (by norm_num) ?_
    simp only [Tammes15.Numerics.sinT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · -- cos dhi ≤ cU
    have h : dhi = (141679/450000) * π := by
      unfold dhi
      ring
    rw [h]
    have hp_le : 3.1415926535 ≤ π := by linarith [Real.pi_gt_d20]
    refine Tammes15.Numerics.cos_mul_pi_le 10 (p := 3.1415926535) (by norm_num) hp_le (by norm_num) (by norm_num) ?_
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · -- cU < 1 / (2 * SU ^ 2) - 1
    norm_num

end Tammes15.Params
