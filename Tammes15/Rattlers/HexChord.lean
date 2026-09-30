import Tammes15.Rattlers.HexPoly
import Tammes15.Numerics.ChordData

/-!
# Proposition onehex: the extreme chord of the inscribed polygon

For `d ∈ [dlo, dhi]`, `h = hrad d` and the step `s = (π - tanAng d h) / 2` of the inscribed polygon of
Proposition onehex (paper, Proposition onehex, inscribed polygon form), the extreme chord of the circle of radius
`h` about one centre keeps the whole disc about the other centre strictly on its side:
`sin h √(cos² h + sin² h cos² (s/2)) < cos h sin d cos (3s/2) + sin h cos (s/2) cos d` (`onehex_chord_margin`).
The worst-end bound over `[dlo, dhi]` has margin about `0.0037` (code/lean/numerics/chord_probe.gp): `hrad`
and `tanAng d (hrad d)` increase with `d`, so every factor is bounded at an end of the interval, and those end
values come from rational enclosures (code/lean/numerics/chord.gp, Numerics/HexData.lean).
-/

open Real

namespace Tammes15

/-- `hrad` increases along `[dlo, dhi]`, with values in `(0, π/2)`. -/
theorem hrad_mem_of_Icc {a b d : ℝ} (ha : dlo ≤ a) (had : a ≤ d) (hdb : d ≤ b) (hb : b ≤ dhi) :
    0 < hrad a ∧ hrad a ≤ hrad d ∧ hrad d ≤ hrad b ∧ hrad b < π / 2 := by
  have hdlo_pos : 0 < dlo := by
    unfold dlo
    nlinarith [Real.pi_pos]
  have hdhi_lt_pi_div_two : dhi < π / 2 := by
    unfold dhi
    nlinarith [Real.pi_pos]
  have ha_pos : 0 < a := by linarith
  have hb_lt_pi_div_two : b < π / 2 := by linarith
  have ha_lt_pi_div_two : a < π / 2 := by linarith
  have hd_lt_pi_div_two : d < π / 2 := by linarith
  have hd_gt_zero : 0 < d := by linarith
  have hb_gt_zero : 0 < b := by linarith
  have ha_bounds := hrad_bounds a ⟨ha_pos, ha_lt_pi_div_two⟩
  have hb_bounds := hrad_bounds b ⟨hb_gt_zero, hb_lt_pi_div_two⟩
  have ha_range : a ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨ha_pos, ha_lt_pi_div_two⟩
  have hd_range : d ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hd_gt_zero, hd_lt_pi_div_two⟩
  have hb_range : b ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hb_gt_zero, hb_lt_pi_div_two⟩
  have h_mono := hrad_strictMonoOn.monotoneOn
  have h_ad : hrad a ≤ hrad d := h_mono ha_range hd_range had
  have h_db : hrad d ≤ hrad b := h_mono hd_range hb_range hdb
  have h0 : 0 < hrad a := by linarith
  have hb_lt : hrad b < π / 2 := by linarith
  exact ⟨h0, h_ad, h_db, hb_lt⟩

/-- The angle at a centre increases along `[dlo, dhi]`. -/
theorem tanAng_hrad_mem_of_Icc {a b d : ℝ} (ha : dlo ≤ a) (had : a ≤ d) (hdb : d ≤ b)
    (hb : b ≤ dhi) :
    tanAng a (hrad a) ≤ tanAng d (hrad d) ∧ tanAng d (hrad d) ≤ tanAng b (hrad b) := by
  have hπ := Real.pi_pos
  have hdlo : 0 < dlo := by unfold dlo; positivity
  have hdhi : dhi < π / 2 := by unfold dhi; nlinarith
  obtain ⟨ha0, had', hdb', hb2⟩ := hrad_mem_of_Icc ha had hdb hb
  have hd0 : 0 < hrad d := lt_of_lt_of_le ha0 had'
  have hdpi : hrad d < π / 2 := lt_of_le_of_lt hdb' hb2
  have hapi : hrad a < π / 2 := lt_of_le_of_lt had' hdpi
  have hbpos : 0 < hrad b := lt_of_lt_of_le hd0 hdb'
  have ha' : 0 ≤ a := by linarith
  have hd' : 0 ≤ d := by linarith
  have hbπ : b < π := by linarith
  have hdπ : d < π := by linarith
  refine ⟨?_, ?_⟩
  · calc tanAng a (hrad a) ≤ tanAng d (hrad a) :=
          tanAng_monotoneOn_l (hrad a) ⟨ha0.le, hapi⟩ ⟨ha', by linarith⟩ ⟨hd', hdπ⟩ had
      _ ≤ tanAng d (hrad d) :=
          tanAng_monotoneOn_h d ⟨hd', hdπ⟩ ⟨ha0.le, hapi⟩ ⟨hd0.le, hdpi⟩ had'
  · calc tanAng d (hrad d) ≤ tanAng b (hrad d) :=
          tanAng_monotoneOn_l (hrad d) ⟨hd0.le, hdpi⟩ ⟨hd', hdπ⟩ ⟨by linarith, hbπ⟩ hdb
      _ ≤ tanAng b (hrad b) :=
          tanAng_monotoneOn_h b ⟨by linarith, hbπ⟩ ⟨hd0.le, hdpi⟩ ⟨hbpos.le, hb2⟩ hdb'

/-- Lower end of the angle at the centre: `X = tan (hrad a) tan (a/2)` with
`X² = (1 - ρ²)/ρ² · sin² (a/2) / cos² (a/2) ≥ (L² - C²)/C² · S² / H²`, `ρ = cos a / cos (a/2) ≤ C / L`, so
`X ≥ m` and `-X ≤ -m ≤ cos Γ`. -/
theorem le_tanAng_hrad {a Γ C L H S m : ℝ} (hc0 : 0 < cos a) (hcC : cos a ≤ C) (hL0 : 0 < L)
    (hL : L ≤ cos (a / 2)) (hCL : C ≤ L) (hH : cos (a / 2) ≤ H) (hS0 : 0 ≤ S) (hS : S ≤ sin (a / 2))
    (hm0 : 0 ≤ m) (hm : m ^ 2 ≤ (L ^ 2 - C ^ 2) / C ^ 2 * (S ^ 2 / H ^ 2)) (hΓ0 : 0 ≤ Γ)
    (hΓπ : Γ ≤ π) (hΓ : -m ≤ cos Γ) : Γ ≤ tanAng a (hrad a) := by
  have hh0 : 0 < cos (a / 2) := lt_of_lt_of_le hL0 hL
  have hC0 : 0 < C := lt_of_lt_of_le hc0 hcC
  have hH0 : 0 < H := lt_of_lt_of_le hh0 hH
  have hsa : 0 ≤ sin (a / 2) := le_trans hS0 hS
  have hρ0 : 0 < cos a / cos (a / 2) := div_pos hc0 hh0
  have hρL : cos a / cos (a / 2) * L ≤ C := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hh0]
    nlinarith
  have hρ1 : cos a / cos (a / 2) ≤ 1 := by
    rw [div_le_one hh0]; linarith
  have htan : tan (hrad a) = √(1 - (cos a / cos (a / 2)) ^ 2) / (cos a / cos (a / 2)) := by
    unfold hrad; exact Real.tan_arccos _
  have htana : tan (a / 2) = sin (a / 2) / cos (a / 2) := Real.tan_eq_sin_div_cos _
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = cos a / cos (a / 2) := ⟨_, rfl⟩
  rw [← hρdef] at hρ0 hρL hρ1 htan
  have h1ρ : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have hX0 : 0 ≤ tan (hrad a) * tan (a / 2) := by rw [htan, htana]; positivity
  have hX2 : (tan (hrad a) * tan (a / 2)) ^ 2 =
      (1 - ρ ^ 2) / ρ ^ 2 * (sin (a / 2) ^ 2 / cos (a / 2) ^ 2) := by
    rw [htan, htana, mul_pow, div_pow, div_pow, Real.sq_sqrt h1ρ]
  have hmX : m ≤ tan (hrad a) * tan (a / 2) := by
    have h2 : m ^ 2 ≤ (tan (hrad a) * tan (a / 2)) ^ 2 := by
      rw [hX2]
      refine le_trans hm ?_
      apply mul_le_mul
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_self_le_mul_self (by positivity) hρL
        nlinarith
      · exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hS0 hS 2) (by positivity)
          (pow_le_pow_left₀ hh0.le hH 2)
      · positivity
      · exact div_nonneg h1ρ (by positivity)
    exact (pow_le_pow_iff_left₀ hm0 hX0 two_ne_zero).mp h2
  unfold tanAng
  apply Numerics.le_arccos_of_le_cos hΓ0 hΓπ
  linarith

/-- The algebraic core of the chord bound: with `ch² + sh² = 1` and `c1² + s1² = 1`,
`ch² + sh² c1² = 1 - sh² s1²`, bounded factor by factor. -/
theorem chord_ineq_of_bounds {ch sh c3 c1 s1 sd cd Rb σa σb k3 k1 m1 sA cB : ℝ}
    (hRb0 : 0 ≤ Rb) (hch : Rb ≤ ch) (hσa0 : 0 ≤ σa) (hsh1 : σa ≤ sh) (hsh2 : sh ≤ σb)
    (hk30 : 0 ≤ k3) (hc3 : k3 ≤ c3) (hk10 : 0 ≤ k1) (hc1 : k1 ≤ c1) (hm10 : 0 ≤ m1) (hs1 : m1 ≤ s1)
    (hsA0 : 0 ≤ sA) (hsd : sA ≤ sd) (hcB0 : 0 ≤ cB) (hcd : cB ≤ cd)
    (hp1 : ch ^ 2 + sh ^ 2 = 1) (hp2 : c1 ^ 2 + s1 ^ 2 = 1)
    (hkey : σb ^ 2 * (1 - σa ^ 2 * m1 ^ 2) < (Rb * sA * k3 + σa * k1 * cB) ^ 2) :
    sh * √(ch ^ 2 + sh ^ 2 * c1 ^ 2) < ch * sd * c3 + sh * c1 * cd := by
  set R := Rb * sA * k3 + σa * k1 * cB with hR
  have hR_nonneg : 0 ≤ R := by
    have h1 : 0 ≤ Rb * sA * k3 := by
      apply mul_nonneg; apply mul_nonneg hRb0 hsA0; exact hk30
    have h2 : 0 ≤ σa * k1 * cB := by
      apply mul_nonneg; apply mul_nonneg hσa0 hk10; exact hcB0
    linarith
  have h_sh_nonneg : 0 ≤ sh := le_trans hσa0 hsh1
  have h_s1_nonneg : 0 ≤ s1 := le_trans hm10 hs1
  have hσb_nonneg : 0 ≤ σb := le_trans h_sh_nonneg hsh2
  -- ch² + sh² c1² = 1 - sh² s1²
  have h_eq1 : ch ^ 2 + sh ^ 2 * c1 ^ 2 = 1 - sh ^ 2 * s1 ^ 2 := by
    have hch_sq : ch ^ 2 = 1 - sh ^ 2 := by linarith
    calc
      ch ^ 2 + sh ^ 2 * c1 ^ 2 = (1 - sh ^ 2) + sh ^ 2 * c1 ^ 2 := by rw [hch_sq]
      _ = 1 - sh ^ 2 * s1 ^ 2 := by
        have hs1_sq : s1 ^ 2 = 1 - c1 ^ 2 := by linarith
        nlinarith
  -- sh² s1² ≥ σa² m1²
  have h_ineq_sq : σa ^ 2 * m1 ^ 2 ≤ sh ^ 2 * s1 ^ 2 := by
    have h_prod : σa * m1 ≤ sh * s1 :=
      mul_le_mul hsh1 hs1 hm10 h_sh_nonneg
    have h_nonneg_left : 0 ≤ σa * m1 := mul_nonneg hσa0 hm10
    have h_nonneg_right : 0 ≤ sh * s1 := mul_nonneg h_sh_nonneg h_s1_nonneg
    nlinarith
  -- 0 ≤ 1 - σa² m1²
  have h_nonneg_inner : 0 ≤ 1 - σa ^ 2 * m1 ^ 2 := by
    have h_nonneg_sum : 0 ≤ ch ^ 2 + sh ^ 2 * c1 ^ 2 := by
      apply add_nonneg (pow_two_nonneg _)
      apply mul_nonneg (pow_two_nonneg _) (pow_two_nonneg _)
    have h_le : ch ^ 2 + sh ^ 2 * c1 ^ 2 ≤ 1 - σa ^ 2 * m1 ^ 2 := by
      rw [h_eq1]
      nlinarith
    linarith
  -- sh * √(ch² + sh² c1²) ≤ σb * √(1 - σa² m1²)
  have h_step4 : sh * √(ch ^ 2 + sh ^ 2 * c1 ^ 2) ≤ σb * √(1 - σa ^ 2 * m1 ^ 2) := by
    have h_sqrt_le : √(ch ^ 2 + sh ^ 2 * c1 ^ 2) ≤ √(1 - σa ^ 2 * m1 ^ 2) :=
      Real.sqrt_le_sqrt (by
        rw [h_eq1]
        nlinarith)
    have h_sqrt_nonneg : 0 ≤ √(ch ^ 2 + sh ^ 2 * c1 ^ 2) := Real.sqrt_nonneg _
    exact mul_le_mul hsh2 h_sqrt_le h_sqrt_nonneg hσb_nonneg
  -- σb * √(1 - σa² m1²) = √(σb² * (1 - σa² m1²))
  have h_step5 : σb * √(1 - σa ^ 2 * m1 ^ 2) = √(σb ^ 2 * (1 - σa ^ 2 * m1 ^ 2)) := by
    calc
      σb * √(1 - σa ^ 2 * m1 ^ 2) = √(σb ^ 2) * √(1 - σa ^ 2 * m1 ^ 2) := by
        rw [Real.sqrt_sq hσb_nonneg]
      _ = √(σb ^ 2 * (1 - σa ^ 2 * m1 ^ 2)) := by
        rw [← Real.sqrt_mul (sq_nonneg σb)]
  -- √(σb² * (1 - σa² m1²)) < R
  have h_step6 : √(σb ^ 2 * (1 - σa ^ 2 * m1 ^ 2)) < R := by
    have h_left_nonneg : 0 ≤ σb ^ 2 * (1 - σa ^ 2 * m1 ^ 2) := by
      apply mul_nonneg (sq_nonneg _)
      exact h_nonneg_inner
    have h_sqrt_lt : √(σb ^ 2 * (1 - σa ^ 2 * m1 ^ 2)) < √(R ^ 2) :=
      Real.sqrt_lt_sqrt h_left_nonneg hkey
    rw [Real.sqrt_sq hR_nonneg] at h_sqrt_lt
    exact h_sqrt_lt
  -- R ≤ ch * sd * c3 + sh * c1 * cd
  have h_step7 : R ≤ ch * sd * c3 + sh * c1 * cd := by
    have h_term1 : Rb * sA * k3 ≤ ch * sd * c3 := by
      have h1 : Rb * sA ≤ ch * sd :=
        mul_le_mul hch hsd hsA0 (le_trans hRb0 hch)
      have h2 : (Rb * sA) * k3 ≤ (ch * sd) * c3 :=
        mul_le_mul h1 hc3 hk30 (mul_nonneg (le_trans hRb0 hch) (le_trans hsA0 hsd))
      simpa [mul_assoc] using h2
    have h_term2 : σa * k1 * cB ≤ sh * c1 * cd := by
      have h1 : σa * k1 ≤ sh * c1 :=
        mul_le_mul hsh1 hc1 hk10 h_sh_nonneg
      have h2 : (σa * k1) * cB ≤ (sh * c1) * cd :=
        mul_le_mul h1 hcd hcB0 (mul_nonneg h_sh_nonneg (le_trans hk10 hc1))
      simpa [mul_assoc] using h2
    linarith
  -- chain everything together
  calc
    sh * √(ch ^ 2 + sh ^ 2 * c1 ^ 2) ≤ σb * √(1 - σa ^ 2 * m1 ^ 2) := h_step4
    _ = √(σb ^ 2 * (1 - σa ^ 2 * m1 ^ 2)) := h_step5
    _ < R := h_step6
    _ ≤ ch * sd * c3 + sh * c1 * cd := h_step7

/-- The chord bound on a piece `[a, b]` of `[dlo, dhi]` from rational bounds at its ends. -/
theorem chord_piece_of {a b d Γ G C L c H1 Rb σa σb k3 k1 m1 sA cB : ℝ}
    (ha : dlo ≤ a) (had : a ≤ d) (hdb : d ≤ b) (hb : b ≤ dhi)
    (hcC : cos a ≤ C) (hL0 : 0 < L) (hL : L ≤ cos (a / 2)) (hσa0 : 0 ≤ σa)
    (hσa : σa ^ 2 ≤ 1 - C ^ 2 / L ^ 2)
    (hc0 : 0 < c) (hc : c ≤ cos b) (hH1 : cos (b / 2) ≤ H1) (hRb0 : 0 ≤ Rb) (hRb : Rb * H1 ≤ c)
    (hσb0 : 0 ≤ σb) (hσb : 1 - Rb ^ 2 ≤ σb ^ 2)
    (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ tanAng a (hrad a)) (hG : tanAng b (hrad b) ≤ G) (hGπ : G ≤ π)
    (hk30 : 0 ≤ k3) (hk3 : k3 ≤ cos (3 * ((π - Γ) / 2) / 2))
    (hk10 : 0 ≤ k1) (hk1 : k1 ≤ cos ((π - Γ) / 4))
    (hm10 : 0 ≤ m1) (hm1 : m1 ≤ sin ((π - G) / 4))
    (hsA0 : 0 ≤ sA) (hsA : sA ≤ sin a) (hcB0 : 0 ≤ cB) (hcB : cB ≤ cos b)
    (hkey : σb ^ 2 * (1 - σa ^ 2 * m1 ^ 2) < (Rb * sA * k3 + σa * k1 * cB) ^ 2) :
    sin (hrad d) * √(cos (hrad d) ^ 2 + sin (hrad d) ^ 2 * cos ((π - tanAng d (hrad d)) / 4) ^ 2) <
      cos (hrad d) * sin d * cos (3 * ((π - tanAng d (hrad d)) / 2) / 2) +
        sin (hrad d) * cos ((π - tanAng d (hrad d)) / 4) * cos d := by
  have hπ := Real.pi_pos
  have hdlo : 0 < dlo := by unfold dlo; positivity
  have hdhi : dhi < π / 2 := by unfold dhi; nlinarith
  obtain ⟨ha0, had', hdb', hb2⟩ := hrad_mem_of_Icc ha had hdb hb
  obtain ⟨hγa, hγb⟩ := tanAng_hrad_mem_of_Icc ha had hdb hb
  have hcosa : 0 < cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcosa2 : 0 < cos (a / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcosb2 : 0 < cos (b / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcosb : 0 < cos b := lt_of_lt_of_le hc0 hc
  -- (1) `Rb ≤ cos (hrad d)`
  have hρb1 : cos b / cos (b / 2) ≤ 1 := by
    rw [div_le_one hcosb2]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hcoshb : cos (hrad b) = cos b / cos (b / 2) := by
    unfold hrad
    exact Real.cos_arccos (by have := div_pos hcosb hcosb2; linarith) hρb1
  have hRbρ : Rb ≤ cos b / cos (b / 2) := by
    rw [le_div_iff₀ hcosb2]
    calc Rb * cos (b / 2) ≤ Rb * H1 := mul_le_mul_of_nonneg_left hH1 hRb0
      _ ≤ c := hRb
      _ ≤ cos b := hc
  have hch : Rb ≤ cos (hrad d) := by
    refine le_trans hRbρ ?_
    rw [← hcoshb]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hdb'
  -- (2) `σa ≤ sin (hrad d)`
  have hρa0 : 0 < cos a / cos (a / 2) := div_pos hcosa hcosa2
  have hρaL : cos a / cos (a / 2) * L ≤ C := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hcosa2]
    calc cos a * L ≤ cos a * cos (a / 2) := mul_le_mul_of_nonneg_left hL hcosa.le
      _ ≤ C * cos (a / 2) := mul_le_mul_of_nonneg_right hcC hcosa2.le
  have hsinha : sin (hrad a) = √(1 - (cos a / cos (a / 2)) ^ 2) := by
    unfold hrad; exact Real.sin_arccos _
  have hsa : σa ≤ sin (hrad a) := by
    rw [hsinha]
    calc σa = √(σa ^ 2) := (Real.sqrt_sq hσa0).symm
      _ ≤ √(1 - (cos a / cos (a / 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have h1 : (cos a / cos (a / 2)) ^ 2 * L ^ 2 ≤ C ^ 2 := by
          have := mul_self_le_mul_self (by positivity) hρaL
          calc (cos a / cos (a / 2)) ^ 2 * L ^ 2 = (cos a / cos (a / 2) * L) * (cos a / cos (a / 2) * L) := by ring
            _ ≤ C * C := this
            _ = C ^ 2 := by ring
        have h2 : (cos a / cos (a / 2)) ^ 2 ≤ C ^ 2 / L ^ 2 := by
          rw [le_div_iff₀ (by positivity)]; exact h1
        linarith
  have hsh1 : σa ≤ sin (hrad d) :=
    le_trans hsa (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) had')
  -- (3) `sin (hrad d) ≤ σb`
  have hsinhb : sin (hrad b) = √(1 - (cos b / cos (b / 2)) ^ 2) := by
    unfold hrad; exact Real.sin_arccos _
  have hsb : sin (hrad b) ≤ σb := by
    rw [hsinhb]
    calc √(1 - (cos b / cos (b / 2)) ^ 2) ≤ √(σb ^ 2) := by
          apply Real.sqrt_le_sqrt
          have := mul_self_le_mul_self hRb0 hRbρ
          have e : (cos b / cos (b / 2)) ^ 2 = (cos b / cos (b / 2)) * (cos b / cos (b / 2)) := by ring
          rw [e]; linarith
      _ = σb := Real.sqrt_sq hσb0
  have hsh2 : sin (hrad d) ≤ σb :=
    le_trans (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hdb') hsb
  -- (4) the step `s = (π - γ) / 2`
  have hγ0 : 0 ≤ tanAng d (hrad d) := by unfold tanAng; exact Real.arccos_nonneg _
  have hγπ : tanAng d (hrad d) ≤ π := by unfold tanAng; exact Real.arccos_le_pi _
  have hΓγ : Γ ≤ tanAng d (hrad d) := le_trans hΓ hγa
  have hγG : tanAng d (hrad d) ≤ G := le_trans hγb hG
  have hc3 : k3 ≤ cos (3 * ((π - tanAng d (hrad d)) / 2) / 2) :=
    le_trans hk3 (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith))
  have hc1 : k1 ≤ cos ((π - tanAng d (hrad d)) / 4) :=
    le_trans hk1 (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith))
  have hs1 : m1 ≤ sin ((π - tanAng d (hrad d)) / 4) :=
    le_trans hm1 (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith))
  -- (5) `sin d` and `cos d`
  have hsd : sA ≤ sin d :=
    le_trans hsA (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) had)
  have hcd : cB ≤ cos d :=
    le_trans hcB (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hdb)
  exact chord_ineq_of_bounds hRb0 hch hσa0 hsh1 hsh2 hk30 hc3 hk10 hc1 hm10 hs1 hsA0 hsd hcB0 hcd
    (Real.cos_sq_add_sin_sq _) (Real.cos_sq_add_sin_sq _) hkey

open Numerics in
/-- Proposition onehex: the extreme chord keeps the other disc strictly on its side. -/
theorem onehex_chord_margin (d : ℝ) (h1 : dlo ≤ d) (h2 : d ≤ dhi) :
    sin (hrad d) * √(cos (hrad d) ^ 2 + sin (hrad d) ^ 2 * cos ((π - tanAng d (hrad d)) / 4) ^ 2) <
      cos (hrad d) * sin d * cos (3 * ((π - tanAng d (hrad d)) / 2) / 2) +
        sin (hrad d) * cos ((π - tanAng d (hrad d)) / 4) * cos d := by
  have ha : dpt 0 = 357719/1200000 * π := by unfold dpt; push_cast; ring
  have ha2 : dpt 0 / 2 = 357719/2400000 * π := by rw [ha]; ring
  have hb : dpt 10 = 141679/450000 * π := by unfold dpt; push_cast; ring
  have hb2 : dpt 10 / 2 = 141679/900000 * π := by rw [hb]; ring
  have hπ := Real.pi_pos
  refine chord_piece_of (a := dpt 0) (b := dpt 10) (Γ := 41569/60000 * π) (G := 4139/5625 * π) (C := 296302953/500000000) (L := 223089521/250000000) (c := 549437037/1000000000) (H1 := 5501131/6250000) (Rb := 624231903/1000000000) (σa := 747652813/1000000000) (σb := 781239101/1000000000) (k3 := 749305453/1000000000) (k1 := 242759351/250000000) (m1 := 205999241/1000000000) (sA := 12585821/15625000) (cB := 549437037/1000000000)
    (by rw [dpt_zero]) (by rw [dpt_zero]; exact h1) (by rw [dpt_ten]; exact h2) (by rw [dpt_ten]) ?_ (by norm_num) ?_ (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity) ?_ ?_ (by nlinarith) (by norm_num) ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num)
  · rw [ha]; exact cos_dpt_le_0
  · rw [ha2]; exact le_cos_hdpt_0
  · rw [hb]; exact le_cos_dpt_10
  · rw [hb2]; exact cos_hdpt_le_10
  · refine le_tanAng_hrad (C := 296302953/500000000) (L := 223089521/250000000) (H := 892358087/1000000000) (S := 112832023/250000000) (m := 284705833/500000000) ?_ ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans (by norm_num) le_cos_chordGam)
    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_0
    · rw [ha]; exact cos_dpt_le_0
    · rw [ha2]; exact le_cos_hdpt_0
    · rw [ha2]; exact cos_hdpt_le_0
    · rw [ha2]; exact le_sin_hdpt_0
  · refine tanAng_hrad_le (c := 549437037/1000000000) (H1 := 5501131/6250000) (H2 := 880180957/1000000000) (S := 94927653/200000000) (M := 16872087/25000000) (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_9 (by norm_num))
    · rw [hb]; exact le_cos_dpt_10
    · rw [hb2]; exact cos_hdpt_le_10
    · rw [hb2]; exact le_cos_hdpt_10
    · rw [hb2, hb]; exact le_trans cos_dpt_le_10 (le_trans (by norm_num) le_cos_hdpt_10)
    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [hb2]; exact sin_hdpt_le_10
  · rw [show 3 * ((π - 41569/60000 * π) / 2) / 2 = 18431/80000 * π by ring]; exact le_cos_chord3
  · rw [show (π - 41569/60000 * π) / 4 = 18431/240000 * π by ring]; exact le_cos_chord1
  · rw [show (π - 4139/5625 * π) / 4 = 743/11250 * π by ring]; exact le_sin_chordG
  · rw [ha]; exact le_sin_dpt_0
  · rw [hb]; exact le_cos_dpt_10

end Tammes15
