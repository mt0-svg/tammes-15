import Tammes15.D3lp.Ranges
import Tammes15.Params.Checks

open Real

namespace Tammes15.D3lp

theorem alpha_hi_S1 : alpha dhiS1 ≤ (1.19407480556942222917 : ℝ) := by
  set a := (1.19407480556942222917 : ℝ) with ha
  set cL := (581962774727757684992812968071 / 1000000000000000000000000000000 : ℝ) with hcL
  have ha0 : 0 ≤ a := by
    unfold a; norm_num
  have haπ : a ≤ π := by
    unfold a; have h := Real.pi_gt_three; nlinarith
  have hcL_pos : 0 < cL := by
    unfold cL; norm_num
  have hdeq : dhiS1 = (4352903 / 14400000 : ℝ) * π := by
    unfold dhiS1; ring
  have h_cL_le : cL ≤ cos dhiS1 := by
    rw [hdeq]
    refine Tammes15.Numerics.le_cos_mul_pi 13 (p := 3.141592653589793238463) Tammes15.Params.pi_lt_d21.le (by norm_num) (by norm_num) ?_
    unfold cL Tammes15.Numerics.cosT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_cos_a_le : cos a ≤ cL / (1 + cL) := by
    refine Tammes15.Numerics.cos_le_of_cosT 13 ha0 ?_
    unfold cL Tammes15.Numerics.cosT a
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  exact Tammes15.Params.alpha_le_of hcL_pos h_cL_le ha0 haπ h_cos_a_le

theorem ssum_hi_S1 : Ssum dhiS1 ≤ (3.67644971787537649676 : ℝ) := by
  set s := (3.67644971787537649676 : ℝ) / 4 with hs_def
  have hs_eq : (3.67644971787537649676 : ℝ) = 4 * s := by
    rw [hs_def]; norm_num
  rw [hs_eq]
  set cL := (581962774727757684992812968071 / 1000000000000000000000000000000 : ℝ) with hcL_def
  set Cu := (606526070476306970598146878409 / 1000000000000000000000000000000 : ℝ) with hCu_def
  set Sl := (99382949826083874599492427743 / 125000000000000000000000000000 : ℝ) with hSl_def
  have hcL_pos : 0 < cL := by rw [hcL_def]; norm_num
  have hs_pos : 0 < s := by rw [hs_def]; norm_num
  have hSl_pos : 0 < Sl := by rw [hSl_def]; norm_num
  refine Tammes15.Params.smax_le_of (d := dhiS1) (s := s) (cL := cL) (Cu := Cu) (Sl := Sl) hcL_pos ?_ hs_pos ?_ ?_ ?_ hSl_pos ?_
  · have hdeq : dhiS1 = (4352903 / 14400000 : ℝ) * π := by
      unfold dhiS1; ring
    rw [hdeq]
    refine Tammes15.Numerics.le_cos_mul_pi 13 (p := 3.141592653589793238463) Tammes15.Params.pi_lt_d21.le (by norm_num) (by norm_num) ?_
    rw [hcL_def]
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · rw [hs_def]
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith
  · refine Tammes15.Numerics.cos_le_of_cosT 13 (by rw [hs_def]; norm_num) ?_
    rw [hCu_def, hs_def]
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · refine Tammes15.Numerics.le_sin_of_sinT 13 (by rw [hs_def]; norm_num) ?_
    rw [hSl_def, hs_def]
    simp only [Tammes15.Numerics.sinT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · rw [hcL_def, hCu_def, hSl_def]
    norm_num

theorem alpha_lo_S2 : (1.19407480556942222916 : ℝ) ≤ alpha dloS2 := by
  set a := (1.19407480556942222916 : ℝ) with ha
  set cU := (581962774727757684993550437673 / 1000000000000000000000000000000 : ℝ) with hcU
  have ha0 : 0 ≤ a := by
    unfold a; norm_num
  have haπ : a ≤ π := by
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    unfold a; nlinarith
  have hdeq : dloS2 = (4352903 / 14400000 : ℝ) * π := by
    unfold dloS2; ring
  have hcos_pos : 0 < cos dloS2 := by
    rw [hdeq]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hcos_le : cos dloS2 ≤ cU := by
    rw [hdeq]
    refine Tammes15.Numerics.cos_mul_pi_le 13 (p := 3.14159265358979323846) ?_ ?_ ?_ ?_ ?_
    · norm_num
    · exact Real.pi_gt_d20.le
    · norm_num
    · norm_num
    · unfold cU Tammes15.Numerics.cosT
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
  have h_cU_div : cU / (1 + cU) ≤ cos a := by
    refine Tammes15.Numerics.le_cos_of_cosT 13 ha0 ?_
    unfold cU a Tammes15.Numerics.cosT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  exact Tammes15.Params.le_alpha_of hcos_pos hcos_le ha0 haπ h_cU_div

theorem alpha_hi_S2 : alpha dhiS2 ≤ (1.19871890275567596783 : ℝ) := by
  set a := (1.19871890275567596783 : ℝ) with ha
  set cL := (114243802446087220435810899349 / 200000000000000000000000000000 : ℝ) with hcL
  have ha0 : 0 ≤ a := by
    unfold a; norm_num
  have haπ : a ≤ π := by
    unfold a; have h := Real.pi_gt_three; nlinarith
  have hcL_pos : 0 < cL := by
    unfold cL; norm_num
  have hdeq : dhiS2 = (2206589 / 7200000 : ℝ) * π := by
    unfold dhiS2; ring
  have h_cL_le : cL ≤ cos dhiS2 := by
    rw [hdeq]
    refine Tammes15.Numerics.le_cos_mul_pi 13 (p := 3.141592653589793238463) Tammes15.Params.pi_lt_d21.le (by norm_num) (by norm_num) ?_
    unfold cL Tammes15.Numerics.cosT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_cos_a_le : cos a ≤ cL / (1 + cL) := by
    refine Tammes15.Numerics.cos_le_of_cosT 13 ha0 ?_
    unfold cL Tammes15.Numerics.cosT a
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  exact Tammes15.Params.alpha_le_of hcL_pos h_cL_le ha0 haπ h_cos_a_le

theorem ssum_hi_S2 : Ssum dhiS2 ≤ (3.69439879742535921844 : ℝ) := by
  set s := (3.69439879742535921844 : ℝ) / 4 with hs_def
  have hs_eq : (3.69439879742535921844 : ℝ) = 4 * s := by
    rw [hs_def]; norm_num
  rw [hs_eq]
  set cL := (114243802446087220435810899349 / 200000000000000000000000000000 : ℝ) with hcL_def
  set Cu := (602952311134244867579979508309 / 1000000000000000000000000000000 : ℝ) with hCu_def
  set Sl := (797777231122744422918004336471 / 1000000000000000000000000000000 : ℝ) with hSl_def
  have hcL_pos : 0 < cL := by rw [hcL_def]; norm_num
  have hs_pos : 0 < s := by rw [hs_def]; norm_num
  have hSl_pos : 0 < Sl := by rw [hSl_def]; norm_num
  refine Tammes15.Params.smax_le_of (d := dhiS2) (s := s) (cL := cL) (Cu := Cu) (Sl := Sl) hcL_pos ?_ hs_pos ?_ ?_ ?_ hSl_pos ?_
  · have hdeq : dhiS2 = (2206589 / 7200000 : ℝ) * π := by
      unfold dhiS2; ring
    rw [hdeq]
    refine Tammes15.Numerics.le_cos_mul_pi 13 (p := 3.141592653589793238463) Tammes15.Params.pi_lt_d21.le (by norm_num) (by norm_num) ?_
    rw [hcL_def]
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · rw [hs_def]
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith
  · refine Tammes15.Numerics.cos_le_of_cosT 13 (by rw [hs_def]; norm_num) ?_
    rw [hCu_def, hs_def]
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · refine Tammes15.Numerics.le_sin_of_sinT 13 (by rw [hs_def]; norm_num) ?_
    rw [hSl_def, hs_def]
    simp only [Tammes15.Numerics.sinT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · rw [hcL_def, hCu_def, hSl_def]
    norm_num

theorem alpha_lo_S3 : (1.19871890275567596782 : ℝ) ≤ alpha dloS3 := by
  set a := (1.19871890275567596782 : ℝ) with ha
  set cU := (571219012230436102179809149907 / 1000000000000000000000000000000 : ℝ) with hcU
  have ha0 : 0 ≤ a := by
    unfold a; norm_num
  have haπ : a ≤ π := by
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    unfold a; nlinarith
  have hdeq : dloS3 = (2206589 / 7200000 : ℝ) * π := by
    unfold dloS3; ring
  have hcos_pos : 0 < cos dloS3 := by
    rw [hdeq]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hcos_le : cos dloS3 ≤ cU := by
    rw [hdeq]
    refine Tammes15.Numerics.cos_mul_pi_le 13 (p := 3.14159265358979323846) ?_ ?_ ?_ ?_ ?_
    · norm_num
    · exact Real.pi_gt_d20.le
    · norm_num
    · norm_num
    · unfold cU Tammes15.Numerics.cosT
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
  have h_cU_div : cU / (1 + cU) ≤ cos a := by
    refine Tammes15.Numerics.le_cos_of_cosT 13 ha0 ?_
    unfold cU a Tammes15.Numerics.cosT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  exact Tammes15.Params.le_alpha_of hcos_pos hcos_le ha0 haπ h_cU_div

theorem alpha_hi_S3 : alpha dhiS3 ≤ (1.20346183887535367676 : ℝ) := by
  set a := (1.20346183887535367676 : ℝ) with ha
  set cL := (112075295012280003145052285201 / 200000000000000000000000000000 : ℝ) with hcL
  have ha0 : 0 ≤ a := by
    unfold a; norm_num
  have haπ : a ≤ π := by
    unfold a; have h := Real.pi_gt_three; nlinarith
  have hcL_pos : 0 < cL := by
    unfold cL; norm_num
  have hdeq : dhiS3 = (1491151 / 4800000 : ℝ) * π := by
    unfold dhiS3; ring
  have h_cL_le : cL ≤ cos dhiS3 := by
    rw [hdeq]
    refine Tammes15.Numerics.le_cos_mul_pi 13 (p := 3.141592653589793238463) Tammes15.Params.pi_lt_d21.le (by norm_num) (by norm_num) ?_
    unfold cL Tammes15.Numerics.cosT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_cos_a_le : cos a ≤ cL / (1 + cL) := by
    refine Tammes15.Numerics.cos_le_of_cosT 13 ha0 ?_
    unfold cL Tammes15.Numerics.cosT a
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  exact Tammes15.Params.alpha_le_of hcL_pos h_cL_le ha0 haπ h_cos_a_le

theorem ssum_hi_S3 : Ssum dhiS3 ≤ (3.71281091619146822148 : ℝ) := by
  set s := (3.71281091619146822148 : ℝ) / 4 with hs_def
  have hs_eq : (3.71281091619146822148 : ℝ) = 4 * s := by
    rw [hs_def]; norm_num
  rw [hs_eq]
  set cL := (112075295012280003145052285201 / 200000000000000000000000000000 : ℝ) with hcL_def
  set Cu := (599273744189777317312880538299 / 1000000000000000000000000000000 : ℝ) with hCu_def
  set Sl := (160108835424503083482455043073 / 200000000000000000000000000000 : ℝ) with hSl_def
  have hcL_pos : 0 < cL := by rw [hcL_def]; norm_num
  have hs_pos : 0 < s := by rw [hs_def]; norm_num
  have hSl_pos : 0 < Sl := by rw [hSl_def]; norm_num
  refine Tammes15.Params.smax_le_of (d := dhiS3) (s := s) (cL := cL) (Cu := Cu) (Sl := Sl) hcL_pos ?_ hs_pos ?_ ?_ ?_ hSl_pos ?_
  · have hdeq : dhiS3 = (1491151 / 4800000 : ℝ) * π := by
      unfold dhiS3; ring
    rw [hdeq]
    refine Tammes15.Numerics.le_cos_mul_pi 13 (p := 3.141592653589793238463) Tammes15.Params.pi_lt_d21.le (by norm_num) (by norm_num) ?_
    rw [hcL_def]
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · rw [hs_def]
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith
  · refine Tammes15.Numerics.cos_le_of_cosT 13 (by rw [hs_def]; norm_num) ?_
    rw [hCu_def, hs_def]
    simp only [Tammes15.Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · refine Tammes15.Numerics.le_sin_of_sinT 13 (by rw [hs_def]; norm_num) ?_
    rw [hSl_def, hs_def]
    simp only [Tammes15.Numerics.sinT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  · rw [hcL_def, hCu_def, hSl_def]
    norm_num

theorem alpha_lo_S4 : (1.20346183887535367675 : ℝ) ≤ alpha dloS4 := by
  set a := (1.20346183887535367675 : ℝ) with ha
  set cU := (35023529691337500982877082569 / 62500000000000000000000000000 : ℝ) with hcU
  have ha0 : 0 ≤ a := by
    unfold a; norm_num
  have haπ : a ≤ π := by
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    unfold a; nlinarith
  have hdeq : dloS4 = (1491151 / 4800000 : ℝ) * π := by
    unfold dloS4; ring
  have hcos_pos : 0 < cos dloS4 := by
    rw [hdeq]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hcos_le : cos dloS4 ≤ cU := by
    rw [hdeq]
    refine Tammes15.Numerics.cos_mul_pi_le 13 (p := 3.14159265358979323846) ?_ ?_ ?_ ?_ ?_
    · norm_num
    · exact Real.pi_gt_d20.le
    · norm_num
    · norm_num
    · unfold cU Tammes15.Numerics.cosT
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
  have h_cU_div : cU / (1 + cU) ≤ cos a := by
    refine Tammes15.Numerics.le_cos_of_cosT 13 ha0 ?_
    unfold cU a Tammes15.Numerics.cosT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  exact Tammes15.Params.le_alpha_of hcos_pos hcos_le ha0 haπ h_cU_div

end Tammes15.D3lp
