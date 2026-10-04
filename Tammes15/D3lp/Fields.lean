import Tammes15.D3lp.Monot
import Tammes15.D3lp.Ends
import Tammes15.D3lp.ParamsData
import Tammes15.D3lp.Ranges

open Real

namespace Tammes15.D3lp

open Tammes15

theorem pFull_alpha_lo : ∀ d, dloFull ≤ d → d ≤ dhiFull → (pFull.alo : ℝ) / pFull.S ≤ alpha d := by
  intro d hdlo hdhi
  have hlo : 0 < dloFull := by
    unfold dloFull
    positivity
  have hhi : dhiFull < π / 2 := by
    unfold dhiFull
    nlinarith [Real.pi_pos]
  have h_alo : (1.18952772983819258225 : ℝ) ≤ alpha dlo := Params.alo_file_le
  have h_eq : (pFull.alo : ℝ) / pFull.S = (1.18952772983819258225 : ℝ) := by
    unfold pFull
    norm_num
  rw [h_eq]
  exact alpha_lo_of_end hlo hhi h_alo d hdlo hdhi

theorem pFull_alpha_hi : ∀ d, dloFull ≤ d → d ≤ dhiFull → alpha d ≤ (pFull.ahi : ℝ) / pFull.S := by
  intro d hlo hhi
  have hlo_pos : 0 < dloFull := by
    unfold dloFull
    positivity
  have hhi_lt : dhiFull < π / 2 := by
    unfold dhiFull
    have h : (566716 : ℝ) / 10000 < 90 := by norm_num
    nlinarith [Real.pi_pos]
  have ha : alpha dhiFull ≤ (pFull.ahi : ℝ) / pFull.S := by
    calc
      alpha dhiFull = alpha dhi := rfl
      _ ≤ (1.20830549335659207180 : ℝ) := Tammes15.Params.alpha_dhi_le_file
      _ = (pFull.ahi : ℝ) / pFull.S := by norm_num [pFull]
  exact alpha_hi_of_end hlo_pos hhi_lt ha d hlo hhi

theorem pFull_ssum_hi : ∀ d, dloFull ≤ d → d ≤ dhiFull → Ssum d ≤ (pFull.shi : ℝ) / pFull.S := by
  have hlo : 0 < dloFull := by
    unfold dloFull
    positivity
  have hhi : dhiFull < π / 2 := by
    unfold dhiFull
    have hπ : 0 < π := Real.pi_pos
    nlinarith
  have h_target : Ssum dhiFull ≤ (pFull.shi : ℝ) / pFull.S := by
    calc
      Ssum dhiFull = Tammes15.Params.smax dhiFull := by
        unfold Ssum Tammes15.Params.smax
        rfl
      _ = Tammes15.Params.smax dhi := by rfl
      _ ≤ (3.73170040409990243346 : ℝ) := Tammes15.Params.smax_dhi_le_file
      _ = (pFull.shi : ℝ) / pFull.S := by
        unfold pFull
        norm_num
  exact ssum_hi_of_end hlo hhi h_target

theorem pS1_alpha_lo : ∀ d, dloS1 ≤ d → d ≤ dhiS1 → (pS1.alo : ℝ) / pS1.S ≤ alpha d := by
  intro d hdlo hdhi
  have hlo : 0 < dloS1 := by
    rw [show dloS1 = (5365785/100000 : ℝ) * (π / 180) from rfl]
    positivity
  have hhi : dhiS1 < π / 2 := by
    rw [show dhiS1 = (544112875/10000000 : ℝ) * (π / 180) from rfl]
    have hπ := Real.pi_pos
    field_simp [hπ.ne.symm]
    nlinarith
  have h_alo : (pS1.alo : ℝ) / pS1.S ≤ alpha dloS1 := by
    have h_const : (pS1.alo : ℝ) / pS1.S = (1.18952772983819258225 : ℝ) := by
      norm_num [pS1]
    have h_eq : dloS1 = dlo := rfl
    rw [h_const, h_eq]
    exact Params.alo_file_le
  exact alpha_lo_of_end hlo hhi h_alo d hdlo hdhi

lemma alpha_strictMonoOn_helper : StrictMonoOn alpha (Set.Ioo 0 (π / 2)) := by
  intro a ha b hb hlt
  rcases ha with ⟨ha_left, ha_right⟩
  rcases hb with ⟨hb_left, hb_right⟩
  have ha_cos_pos : 0 < cos a := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith
  have hb_cos_pos : 0 < cos b := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith
  have h_cos_lt : cos b < cos a := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hlt
  have hpos1 : 0 < 1 + cos b := by linarith
  have hpos2 : 0 < 1 + cos a := by linarith
  have h_div_lt : cos b / (1 + cos b) < cos a / (1 + cos a) := by
    field_simp [hpos1.ne.symm, hpos2.ne.symm]
    nlinarith
  have h_div_ge_neg_one : -1 ≤ cos b / (1 + cos b) := by
    have h_nonneg : 0 ≤ cos b / (1 + cos b) := by
      apply div_nonneg <;> linarith
    linarith
  have h_div_le_one : cos a / (1 + cos a) ≤ 1 := by
    apply (div_le_one hpos2).mpr
    linarith
  exact Real.arccos_lt_arccos h_div_ge_neg_one h_div_lt h_div_le_one

lemma alpha_hi_of_end' {lo hi a : ℝ} (hlo : 0 < lo) (hhi : hi < π / 2)
    (h : alpha hi ≤ a) : ∀ d, lo ≤ d → d ≤ hi → alpha d ≤ a := by
  intro d hdlo hdhi
  have hd_mem : d ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    constructor <;> linarith
  have hhi_mem : hi ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    constructor <;> linarith
  have h_alpha_d_le_alpha_hi : alpha d ≤ alpha hi :=
    alpha_strictMonoOn_helper.monotoneOn hd_mem hhi_mem hdhi
  linarith

theorem pS1_alpha_hi : ∀ d, dloS1 ≤ d → d ≤ dhiS1 → alpha d ≤ (pS1.ahi : ℝ) / pS1.S := by
  have h_dloS1_pos : 0 < dloS1 := by
    unfold dloS1
    positivity
  have h_dhiS1_lt_pi_div_two : dhiS1 < π / 2 := by
    unfold dhiS1
    have hpi_pos : 0 < π := Real.pi_pos
    nlinarith

  have h_alpha_dhiS1_le : alpha dhiS1 ≤ (pS1.ahi : ℝ) / pS1.S := by

    have h_const : (pS1.ahi : ℝ) / pS1.S = (1.19407480556942222917 : ℝ) := by
      unfold pS1
      norm_num
    rw [h_const]

    exact alpha_hi_S1
  intro d hdlo hdhi
  exact alpha_hi_of_end' h_dloS1_pos h_dhiS1_lt_pi_div_two h_alpha_dhiS1_le d hdlo hdhi

theorem pS1_ssum_hi : ∀ d, dloS1 ≤ d → d ≤ dhiS1 → Ssum d ≤ (pS1.shi : ℝ) / pS1.S := by
  have hlo : 0 < dloS1 := by
    unfold dloS1
    positivity
  have hhi : dhiS1 < π / 2 := by
    unfold dhiS1
    nlinarith [Real.pi_pos]
  have hRHS : (pS1.shi : ℝ) / pS1.S = (3.67644971787537649676 : ℝ) := by
    simp [pS1]
    norm_num
  have h := ssum_hi_of_end hlo hhi ssum_hi_S1
  intro d hdlo hdhi
  have hSsum := h d hdlo hdhi
  rw [hRHS]
  exact hSsum

theorem pS2_alpha_lo : ∀ d, dloS2 ≤ d → d ≤ dhiS2 → (pS2.alo : ℝ) / pS2.S ≤ alpha d := by
  intro d hdlo hdhi
  have hlo_pos : 0 < dloS2 := by
    unfold dloS2
    positivity
  have hhi_lt : dhiS2 < π / 2 := by
    unfold dhiS2
    nlinarith [Real.pi_pos]
  have ha : (pS2.alo : ℝ) / pS2.S ≤ alpha dloS2 := by
    have h_eq : (pS2.alo : ℝ) / pS2.S = (1.19407480556942222916 : ℝ) := by
      norm_num [pS2]
    rw [h_eq]
    exact alpha_lo_S2
  have h := alpha_lo_of_end hlo_pos hhi_lt ha
  exact h d hdlo hdhi

theorem pS2_alpha_hi : ∀ d, dloS2 ≤ d → d ≤ dhiS2 → alpha d ≤ (pS2.ahi : ℝ) / pS2.S := by
  intro d hdlo hdhi
  have hlo_pos : 0 < dloS2 := by
    unfold dloS2
    positivity
  have hhi_lt_pi_div_two : dhiS2 < π / 2 := by
    unfold dhiS2
    nlinarith [Real.pi_pos]
  have h_alpha_hi : alpha dhiS2 ≤ (pS2.ahi : ℝ) / pS2.S := by
    have : (pS2.ahi : ℝ) / pS2.S = (1.19871890275567596783 : ℝ) := by
      unfold pS2
      norm_num
    rw [this]
    exact alpha_hi_S2
  exact alpha_hi_of_end hlo_pos hhi_lt_pi_div_two h_alpha_hi d hdlo hdhi

theorem pS2_ssum_hi : ∀ d, dloS2 ≤ d → d ≤ dhiS2 → Ssum d ≤ (pS2.shi : ℝ) / pS2.S := by
  intro d hdlo hdhi
  have hS : (pS2.shi : ℝ) / pS2.S = (3.69439879742535921844 : ℝ) := by
    norm_num [pS2]
  rw [hS]
  have hpos : 0 < dloS2 := by
    unfold dloS2
    positivity
  have hhi : dhiS2 < π / 2 := by
    unfold dhiS2
    nlinarith [Real.pi_pos]
  have h_upper : Ssum dhiS2 ≤ (3.69439879742535921844 : ℝ) := ssum_hi_S2
  exact ssum_hi_of_end hpos hhi h_upper d hdlo hdhi

theorem pS3_alpha_lo : ∀ d, dloS3 ≤ d → d ≤ dhiS3 → (pS3.alo : ℝ) / pS3.S ≤ alpha d := by
  have hlo : 0 < dloS3 := by
    unfold dloS3
    positivity
  have hhi : dhiS3 < π / 2 := by
    unfold dhiS3
    nlinarith [Real.pi_pos]
  have h_alo_eq : (pS3.alo : ℝ) / pS3.S = (1.19871890275567596782 : ℝ) := by
    unfold pS3
    norm_num
  have h_alo_S3 : (pS3.alo : ℝ) / pS3.S ≤ alpha dloS3 := by
    rw [h_alo_eq]
    exact alpha_lo_S3
  exact alpha_lo_of_end hlo hhi h_alo_S3

lemma div_one_add_le_div_one_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b) : a / (1 + a) ≤ b / (1 + b) := by
  have ha' : 0 < 1 + a := by linarith
  have hb' : 0 < 1 + b := by linarith
  have hsub : 0 ≤ b / (1 + b) - a / (1 + a) := by
    field_simp [ha'.ne.symm, hb'.ne.symm]
    nlinarith
  linarith

theorem pS3_alpha_hi : ∀ d, dloS3 ≤ d → d ≤ dhiS3 → alpha d ≤ (pS3.ahi : ℝ) / pS3.S := by
  intro d hdlo hdhi
  have hpi_pos : 0 < π := Real.pi_pos
  have hpos : 0 < dloS3 := by
    unfold dloS3
    positivity
  have hpi2 : dhiS3 < π / 2 := by
    unfold dhiS3
    nlinarith
  have h0d : 0 ≤ d := le_trans (le_of_lt hpos) hdlo
  have hdpi2 : d ≤ π / 2 := le_trans hdhi (le_of_lt hpi2)
  have h0hi : 0 ≤ dhiS3 := le_trans (le_of_lt hpos) (le_trans hdlo hdhi)
  have hhipi : dhiS3 ≤ π := le_trans (le_of_lt hpi2) (by linarith)
  have hcos_nonneg_d : 0 ≤ cos d :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hdpi2
  have hcos_nonneg_hi : 0 ≤ cos dhiS3 :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (le_of_lt hpi2)
  have hcos : cos dhiS3 ≤ cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0d hhipi hdhi
  have hfrac : cos dhiS3 / (1 + cos dhiS3) ≤ cos d / (1 + cos d) :=
    div_one_add_le_div_one_add hcos_nonneg_hi hcos_nonneg_d hcos
  have halpha : alpha d ≤ alpha dhiS3 := by
    unfold alpha
    exact Real.arccos_le_arccos hfrac
  have hRHS : (pS3.ahi : ℝ) / pS3.S = (1.20346183887535367676 : ℝ) := by
    unfold pS3
    norm_num
  rw [hRHS]
  exact le_trans halpha alpha_hi_S3

theorem pS3_ssum_hi : ∀ d, dloS3 ≤ d → d ≤ dhiS3 → Ssum d ≤ (pS3.shi : ℝ) / pS3.S := by
  have hpos : 0 < dloS3 := by
    unfold dloS3
    have hpi : 0 < π := Real.pi_pos
    nlinarith
  have hhi : dhiS3 < π / 2 := by
    unfold dhiS3
    have hpi : 0 < π := Real.pi_pos
    nlinarith
  have hval : (pS3.shi : ℝ) / pS3.S = (3.71281091619146822148 : ℝ) := by
    unfold pS3
    norm_num
  have hSsum : Ssum dhiS3 ≤ (pS3.shi : ℝ) / pS3.S := by
    rw [hval]
    exact ssum_hi_S3
  intro d hdlo hdhi
  exact ssum_hi_of_end hpos hhi hSsum d hdlo hdhi

theorem pS4_alpha_lo : ∀ d, dloS4 ≤ d → d ≤ dhiS4 → (pS4.alo : ℝ) / pS4.S ≤ alpha d := by
  intro d hdlo hdhi
  have h_alo_div_S : (pS4.alo : ℝ) / pS4.S = (1.20346183887535367675 : ℝ) := by
    unfold pS4
    norm_num
  rw [h_alo_div_S]
  have hpos : 0 < dloS4 := by
    unfold dloS4
    positivity
  have hhi : dhiS4 < π / 2 := by
    unfold dhiS4
    nlinarith [Real.pi_pos]
  exact alpha_lo_of_end hpos hhi alpha_lo_S4 d hdlo hdhi

theorem pS4_alpha_hi : ∀ d, dloS4 ≤ d → d ≤ dhiS4 → alpha d ≤ (pS4.ahi : ℝ) / pS4.S := by
  intro d hlo hhi
  have hdlo_pos : 0 < dloS4 := by
    unfold dloS4
    have hπ := Real.pi_pos
    nlinarith
  have hdhi_lt_pi_div_2 : dhiS4 < π / 2 := by
    unfold dhiS4
    have hπ := Real.pi_pos
    nlinarith
  have h_alpha_dhi_le : alpha dhiS4 ≤ (pS4.ahi : ℝ) / pS4.S := by
    have h_eq : (pS4.ahi : ℝ) / pS4.S = (1.20830549335659207180 : ℝ) := by
      unfold pS4
      norm_num
    rw [h_eq]
    have h_dhi_eq : dhiS4 = dhi := rfl
    rw [h_dhi_eq]
    exact Tammes15.Params.alpha_dhi_le_file
  exact alpha_hi_of_end hdlo_pos hdhi_lt_pi_div_2 h_alpha_dhi_le d hlo hhi

theorem pS4_ssum_hi : ∀ d, dloS4 ≤ d → d ≤ dhiS4 → Ssum d ≤ (pS4.shi : ℝ) / pS4.S := by
  intro d hdlo hdhi
  have h := ssum_hi_of_end (lo := dloS4) (hi := dhiS4) (a := (pS4.shi : ℝ) / pS4.S) (by
    unfold dloS4
    positivity) (by
    unfold dhiS4
    nlinarith [Real.pi_pos]) (by
    have hSsum_eq : Ssum dhiS4 = Params.smax dhi := rfl
    rw [hSsum_eq]
    have hle : Params.smax dhi ≤ (3.73170040409990243346 : ℝ) := Params.smax_dhi_le_file
    have hval : (pS4.shi : ℝ) / pS4.S = (3.73170040409990243346 : ℝ) := by
      unfold pS4
      norm_num
    rw [hval]
    exact hle)
  exact h d hdlo hdhi

end Tammes15.D3lp
