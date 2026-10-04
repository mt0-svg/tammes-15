import Tammes15.D3Prog.L2B.Base

namespace D3Prog.L2B

open Real Tammes15 D3Ck2Spec D3Prog.L2

set_option linter.unusedVariables false

theorem K28_pent_eval_0 (G : Prop) (X0L X0H X1L X1H DL DH : ℤ) (EL EH B1L B1H FL FH B3L B3H GaL GaH TL TH OL OH : ℤ)
    (he : G → ∀ d u : ℝ, Enc DL DH d → Enc X0L X0H u → AF true EL EH (ebase d u))
    (hb1 : G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc X0L X0H u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : G → ∀ d u : ℝ, Enc DL DH d → Enc X1L X1H u → AF true FL FH (ebase d u))
    (hb3 : G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc X1L X1H u → 0 < u → u < 2 * π →
      Enc B3L B3H (bangle d u))
    (hg : G → ∀ θg θe θf : ℝ, AF false DL DH θg → AF true EL EH θe → AF true FL FH θf →
      Enc GaL GaH (gam θg θe θf))
    (ht : ∀ r s : ℝ, Enc B1L B1H r → Enc GaL GaH s → Enc TL TH (r + s))
    (ho : ∀ r s : ℝ, Enc TL TH r → Enc B3L B3H s → Enc OL OH (r + s)) :
    G → ∀ d x y : ℝ, Enc DL DH d → Enc X0L X0H x → Enc X1L X1H y → 0 < d → d < π / 2 → 0 < x → x < 2 * π →
      0 < y → y < 2 * π → Enc OL OH (pentOut 0 d x y) := by
  intro hG d x y hd hx hy hd0 hd1 hx0 hx1 hy0 hy1
  have hg_enc : Enc GaL GaH (gam d (ebase d x) (ebase d y)) :=
    hg hG d (ebase d x) (ebase d y) hd (he hG d x hd hx) (hf hG d y hd hy)
  have hb1_enc : Enc B1L B1H (bangle d x) :=
    hb1 hG d x hd0 hd1 hd hx hx0 hx1
  have hb3_enc : Enc B3L B3H (bangle d y) :=
    hb3 hG d y hd0 hd1 hd hy hy0 hy1
  have ht_enc : Enc TL TH (bangle d x + gam d (ebase d x) (ebase d y)) :=
    ht (bangle d x) (gam d (ebase d x) (ebase d y)) hb1_enc hg_enc
  have ho_enc : Enc OL OH ((bangle d x + gam d (ebase d x) (ebase d y)) + bangle d y) :=
    ho (bangle d x + gam d (ebase d x) (ebase d y)) (bangle d y) ht_enc hb3_enc
  simpa [pentOut, add_assoc] using ho_enc

theorem K28_pent_eval_1 (G : Prop) (X0L X0H X1L X1H DL DH : ℤ) (EL EH B1L B1H FL FH GaL GaH OL OH : ℤ)
    (he : G → ∀ d u : ℝ, Enc DL DH d → Enc X0L X0H u → AF true EL EH (ebase d u))
    (hb1 : G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc X0L X0H u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : G → ∀ d u : ℝ, Enc DL DH d → Enc X1L X1H u → AF true FL FH (ebase d u))
    (hg : G → ∀ θg θe θf : ℝ, AF true FL FH θg → AF true EL EH θe → AF false DL DH θf →
      Enc GaL GaH (gam θg θe θf))
    (ho : ∀ r s : ℝ, Enc B1L B1H r → Enc GaL GaH s → Enc OL OH (r + s)) :
    G → ∀ d x y : ℝ, Enc DL DH d → Enc X0L X0H x → Enc X1L X1H y → 0 < d → d < π / 2 → 0 < x → x < 2 * π →
      0 < y → y < 2 * π → Enc OL OH (pentOut 1 d x y) := by
  intro hG d x y hd hx hy hd0 hd1 hx0 hx1 hy0 hy1
  have hpent : pentOut 1 d x y = bangle d x + gam (ebase d y) (ebase d x) d := by
    simp [pentOut]
  rw [hpent]
  have hgam : Enc GaL GaH (gam (ebase d y) (ebase d x) d) :=
    hg hG (ebase d y) (ebase d x) d (hf hG d y hd hy) (he hG d x hd hx) hd
  have hbangle : Enc B1L B1H (bangle d x) :=
    hb1 hG d x hd0 hd1 hd hx hx0 hx1
  exact ho (bangle d x) (gam (ebase d y) (ebase d x) d) hbangle hgam

theorem K30_N0 (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : InDom F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C : ℤ)
    (side : ℕ) (EL EH B1L B1H FL FH B3L B3H GaL GaH TL TH OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (he : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EL EH (ebase d u))
    (hb1 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true FL FH (ebase d u))
    (hb3 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc Y0 Y1 u → 0 < u → u < 2 * π →
      Enc B3L B3H (bangle d u))
    (hg : True → ∀ θg θe θf : ℝ, AF false D0 D1 θg → AF true EL EH θe → AF true FL FH θf →
      Enc GaL GaH (gam θg θe θf))
    (ht : ∀ r s : ℝ, Enc B1L B1H r → Enc GaL GaH s → Enc TL TH (r + s))
    (ho : ∀ r s : ℝ, Enc TL TH r → Enc B3L B3H s → Enc OL OH (r + s))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaim 0 hi F0 F1 F2 F3 := by
  intro d x y hd_low hd_high hx_low hx_high hy_low hy_high hx_pi hy_pi hfan
  rcases hD with ⟨hF0_lt, hF1_lt, hF2_lt, hF3_lt, hF0_lo, hF0_hi, hF1_lo, hF1_hi, hF2_lo, hF2_hi⟩
  have h_pi_gt_two : (2 : ℝ) < π := by linarith [Real.pi_gt_three]
  have hd_pos : 0 < d := by linarith
  have hd_lt_pi_div_2 : d < π / 2 := by
    have hd_le_one : d ≤ 1 := by linarith
    linarith
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  have hx_lt_2pi : x < 2 * π := by linarith
  have hy_lt_2pi : y < 2 * π := by linarith
  have hd_enc : Enc D0 D1 d := enc_fld hD0 hD1 hd_low hd_high
  have hx_enc : Enc X0 X1 x := enc_fld hX0 hX1 hx_low hx_high
  have hy_enc : Enc Y0 Y1 y := enc_fld hY0 hY1 hy_low hy_high
  have hb1_enc : Enc B1L B1H (bangle d x) :=
    hb1 trivial d x hd_pos hd_lt_pi_div_2 hd_enc hx_enc hx_pos hx_lt_2pi
  have hf_enc : AF true FL FH (ebase d y) := hf trivial d y hd_enc hy_enc
  have hb3_enc : Enc B3L B3H (bangle d y) :=
    hb3 trivial d y hd_pos hd_lt_pi_div_2 hd_enc hy_enc hy_pos hy_lt_2pi
  have he_enc : AF true EL EH (ebase d x) := he trivial d x hd_enc hx_enc
  have hg_enc : Enc GaL GaH (gam d (ebase d x) (ebase d y)) :=
    hg trivial d (ebase d x) (ebase d y) hd_enc he_enc hf_enc
  have ht_enc : Enc TL TH (bangle d x + gam d (ebase d x) (ebase d y)) :=
    ht (bangle d x) (gam d (ebase d x) (ebase d y)) hb1_enc hg_enc
  have henc : Enc OL OH (pentOut 0 d x y) := by
    have h := ho (bangle d x + gam d (ebase d x) (ebase d y)) (bangle d y) ht_enc hb3_enc
    simpa [pentOut] using h
  have hclaim : Claim hi ((C : ℝ) / 2 ^ 28) (pentOut 0 d x y) :=
    claim_of_check hi side C OL OH lo_ok hi_ok cl hside hlo_ok hhi_ok hcl hck (pentOut 0 d x y) henc
  have hdiv : (C : ℝ) / 2 ^ 28 = fld F3 0 := div_fld hC
  simpa [hdiv] using hclaim

theorem K30_N1 (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : InDom F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C : ℤ)
    (side : ℕ) (EL EH B1L B1H FL FH GaL GaH OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (he : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EL EH (ebase d u))
    (hb1 : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc B1L B1H (bangle d u))
    (hf : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true FL FH (ebase d u))
    (hg : True → ∀ θg θe θf : ℝ, AF true FL FH θg → AF true EL EH θe → AF false D0 D1 θf →
      Enc GaL GaH (gam θg θe θf))
    (ho : ∀ r s : ℝ, Enc B1L B1H r → Enc GaL GaH s → Enc OL OH (r + s))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaim 1 hi F0 F1 F2 F3 := by
  intro d x y hd0 hd32 hx0 hx32 hy0 hy32 hx_lt_pi hy_lt_pi hfan
  rcases hD with ⟨hF0, hF1, hF2, hF3, hF0_lo, hF0_hi, hF1_lo, hF1_hi, hF2_lo, hF2_hi⟩
  have hd_pos : 0 < d := by
    have : 0.9 ≤ fld F0 0 := hF0_lo
    linarith
  have hd_lt_pi_div_2 : d < π / 2 := by
    have : fld F0 32 ≤ 1 := hF0_hi
    have h_pi_gt_two : 2 < π := by linarith [Real.pi_gt_three]
    linarith
  have hx_pos : 0 < x := by
    have : 1.1 ≤ fld F1 0 := hF1_lo
    linarith
  have hx_lt_2pi : x < 2 * π := by
    have : fld F1 32 ≤ 3.2 := hF1_hi
    have h_pi_gt_three : 3 < π := Real.pi_gt_three
    linarith
  have h_enc_D0_D1_d : Enc D0 D1 d := enc_fld hD0 hD1 hd0 hd32
  have h_enc_X0_X1_x : Enc X0 X1 x := enc_fld hX0 hX1 hx0 hx32
  have h_enc_Y0_Y1_y : Enc Y0 Y1 y := enc_fld hY0 hY1 hy0 hy32
  have h_enc_bangle : Enc B1L B1H (bangle d x) :=
    hb1 trivial d x hd_pos hd_lt_pi_div_2 h_enc_D0_D1_d h_enc_X0_X1_x hx_pos hx_lt_2pi
  have h_af_ebase_y : AF true FL FH (ebase d y) :=
    hf trivial d y h_enc_D0_D1_d h_enc_Y0_Y1_y
  have h_af_ebase_x : AF true EL EH (ebase d x) :=
    he trivial d x h_enc_D0_D1_d h_enc_X0_X1_x
  have h_af_false : AF false D0 D1 d := h_enc_D0_D1_d
  have h_enc_gam : Enc GaL GaH (gam (ebase d y) (ebase d x) d) :=
    hg trivial (ebase d y) (ebase d x) d h_af_ebase_y h_af_ebase_x h_af_false
  have h_enc_sum : Enc OL OH (bangle d x + gam (ebase d y) (ebase d x) d) :=
    ho (bangle d x) (gam (ebase d y) (ebase d x) d) h_enc_bangle h_enc_gam
  have h_pent : pentOut 1 d x y = bangle d x + gam (ebase d y) (ebase d x) d := by
    simp [pentOut]
  rw [h_pent]
  have h_claim : Claim hi (fld F3 0) (bangle d x + gam (ebase d y) (ebase d x) d) := by
    have h := claim_of_check hi side C OL OH lo_ok hi_ok cl hside hlo_ok hhi_ok hcl hck
      (bangle d x + gam (ebase d y) (ebase d x) d) h_enc_sum
    rw [div_fld hC] at h
    exact h
  exact h_claim

end D3Prog.L2B
