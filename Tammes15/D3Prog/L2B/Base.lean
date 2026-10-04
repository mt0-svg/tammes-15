import Tammes15.D3Prog.L2.Kinds2
import Tammes15.Contractors.Fan

namespace D3Prog.L2B

open Real Tammes15 D3Ck2Spec D3Prog.L2

theorem pi_lo_lt : (843314856 : ℝ) < 2 ^ 28 * π := by
  have := Real.pi_gt_d20
  nlinarith

theorem pi_hi_gt : 2 ^ 28 * π < (843314857 : ℝ) := by
  have := Real.pi_lt_d20
  nlinarith

theorem Enc.le {lo hi : ℤ} {r : ℝ} (h : Enc lo hi r) : lo ≤ hi := by
  have : (lo : ℝ) ≤ hi := h.1.trans h.2
  exact_mod_cast this

theorem enc_of_mem {lo hi : ℤ} {r : ℝ} (h1 : (lo : ℝ) / 2 ^ 28 ≤ r) (h2 : r ≤ (hi : ℝ) / 2 ^ 28) : Enc lo hi r := by
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (by norm_num)] at h1; linarith
  · rw [le_div_iff₀ (by norm_num)] at h2; linarith

theorem mem_of_enc {lo hi : ℤ} {r : ℝ} (h : Enc lo hi r) : (lo : ℝ) / 2 ^ 28 ≤ r ∧ r ≤ (hi : ℝ) / 2 ^ 28 := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (by norm_num)]; linarith
  · rw [le_div_iff₀ (by norm_num)]; linarith

theorem arccos_clamp (y : ℝ) : arccos y = arccos (max (-1) (min 1 y)) := by
  rcases le_total y (-1) with h | h
  · rw [Real.arccos_of_le_neg_one h, min_eq_right (by linarith), max_eq_left h, Real.arccos_neg_one]
  rcases le_total 1 y with h' | h'
  · rw [Real.arccos_of_one_le h', min_eq_left h', max_eq_right (by norm_num), Real.arccos_one]
  · rw [min_eq_right h', max_eq_right h]

theorem enc_arccos_top (y : ℝ) : Enc 0 843314857 (arccos y) := by
  refine ⟨?_, ?_⟩
  · have := Real.arccos_nonneg y
    push_cast; positivity
  · have h1 := Real.arccos_le_pi y
    have h2 := pi_hi_gt
    push_cast; nlinarith

theorem cot_of_sin_eq_zero {x : ℝ} (h : sin x = 0) : cot x = 0 := by
  rw [Real.cot_eq_cos_div_sin, h, div_zero]

theorem fan_sign_of_open (d u z : ℝ) (hd : 0 < d ∧ d < π / 2) (hu : 0 < u ∧ u ≤ π)
    (h : 0 < arccos z → arccos z < π → 0 ≤ cos d * sin (u / 2) + cot (arccos z) * cos (u / 2)) :
    0 ≤ cos d * sin (u / 2) + cot (arccos z) * cos (u / 2) := by
  rcases (Real.arccos_nonneg z).lt_or_eq with h0 | h0
  · rcases (Real.arccos_le_pi z).lt_or_eq with h1 | h1
    · exact h h0 h1
    · rw [h1, cot_of_sin_eq_zero Real.sin_pi, zero_mul, add_zero]
      have := Real.cos_pos_of_mem_Ioo ⟨by linarith, hd.2⟩
      have := Real.sin_nonneg_of_nonneg_of_le_pi (x := u / 2) (by linarith) (by linarith)
      positivity
  · rw [← h0, cot_of_sin_eq_zero Real.sin_zero, zero_mul, add_zero]
    have := Real.cos_pos_of_mem_Ioo ⟨by linarith, hd.2⟩
    have := Real.sin_nonneg_of_nonneg_of_le_pi (x := u / 2) (by linarith) (by linarith)
    positivity

theorem claim_of_check (hi : Bool) (side : ℕ) (C OL OH : ℤ) (lo_ok hi_ok cl : ℕ) (hside : side = 1 ↔ hi = true)
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) (r : ℝ) (hr : Enc OL OH r) : Claim hi ((C : ℝ) / 2 ^ 28) r := by
  have hcl1 : cl = 1 := hck trivial
  obtain ⟨h1, h2⟩ := mem_of_enc hr
  unfold Claim
  by_cases hs : side = 1
  · simp only [hside.1 hs, ↓reduceIte]
    simp only [hcl, hs, ↓reduceIte] at hcl1
    have : (OH : ℝ) ≤ C := by exact_mod_cast hhi_ok.1 hcl1
    have : (OH : ℝ) / 2 ^ 28 ≤ (C : ℝ) / 2 ^ 28 := by gcongr
    linarith
  · have hh : hi = false := by
      cases hi
      · rfl
      · exact absurd (hside.2 rfl) hs
    simp only [hh, Bool.false_eq_true, ↓reduceIte]
    simp only [hcl, hs, ↓reduceIte] at hcl1
    have : (C : ℝ) ≤ OL := by exact_mod_cast hlo_ok.1 hcl1
    have : (C : ℝ) / 2 ^ 28 ≤ (OL : ℝ) / 2 ^ 28 := by gcongr
    linarith

theorem fld_eq (F s : ℕ) : 2 ^ 28 * fld F s = (((F / 2 ^ s % 2 ^ 32 * 16 : ℕ) : ℤ) : ℝ) :=
  (K1_ix F s _ rfl).symm

theorem enc_fld {F : ℕ} {V W : ℤ} (hV : V = ((F / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hW : W = ((F / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) {x : ℝ} (h1 : fld F 0 ≤ x) (h2 : x ≤ fld F 32) : Enc V W x := by
  subst hV hW
  refine ⟨?_, ?_⟩
  · rw [← fld_eq]; linarith
  · rw [← fld_eq]; linarith

theorem div_fld {F s : ℕ} {V : ℤ} (hV : V = ((F / 2 ^ s % 2 ^ 32 * 16 : ℕ) : ℤ)) : (V : ℝ) / 2 ^ 28 = fld F s := by
  subst hV
  rw [← fld_eq]
  field_simp

theorem decDirX_early {lo hi d : ℝ} (Y : ℝ → ℝ) (hlo : 0 < lo) (hd0 : 0 < d ∧ d < π / 2) (bxhi : ℝ)
    (hbx : ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π → bangle d u + Y u ≤ bxhi) (hbxpi : bxhi ≤ π) :
    ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π → 0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  intro u hu hYpos hYlt
  have hu_le_pi : u ≤ π := hu.2.trans (min_le_right _ _)
  have hu_pos : 0 < u := hlo.trans_le hu.1
  have hcos_d_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith [hd0.1], hd0.2⟩
  have hsum_le_pi : bangle d u + Y u ≤ π := (hbx u hu hYpos hYlt).trans hbxpi
  by_cases hu_eq_pi : u = π
  · subst hu_eq_pi
    have h_target_eq : cos d * sin (π / 2) + cot (Y π) * cos (π / 2) = cos d := by
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.cot_eq_cos_div_sin]
    rw [h_target_eq]
    exact hcos_d_pos.le
  · have hu_lt_pi : u < π := lt_of_le_of_ne hu_le_pi hu_eq_pi
    have hcos_u2_pos : 0 < cos (u / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hsin_u2_pos : 0 < sin (u / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hbangle_pos : 0 < bangle d u := by
      rw [bangle]
      exact Real.arctan_pos.mpr (div_pos hcos_u2_pos (mul_pos hcos_d_pos hsin_u2_pos))
    have hsin_sum_nonneg : 0 ≤ sin (bangle d u + Y u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hsum_le_pi
    have hbangle_lt : bangle d u < π / 2 := Real.arctan_lt_pi_div_two _
    have hsin_bangle_pos : 0 < sin (bangle d u) :=
      Real.sin_pos_of_pos_of_lt_pi hbangle_pos (by linarith [Real.pi_pos])
    have hsin_Y_pos : 0 < sin (Y u) := Real.sin_pos_of_pos_of_lt_pi hYpos hYlt
    rw [Tammes15.fan_sign_identity d u (Y u) hd0 ⟨hu_pos, hu_lt_pi⟩ ⟨hYpos, hYlt⟩]
    exact div_nonneg (mul_nonneg hcos_u2_pos.le hsin_sum_nonneg) (mul_nonneg hsin_bangle_pos.le hsin_Y_pos.le)

theorem gam_swap (g e f : ℝ) : gam g e f = gam g f e := by
  simp only [gam, eta, mul_comm]

theorem pentOut0_antitoneOn_x {d y p q : ℝ} (hd : 0 < d ∧ d < π / 2) (hy : 0 < y ∧ y ≤ π) (hp : 0 < p)
    (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta d (ebase d u) (ebase d y) → eta d (ebase d u) (ebase d y) < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam (ebase d y) (ebase d u) d) * cos (u / 2)) :
    AntitoneOn (fun u => pentOut 0 d u y) (Set.Icc p q) := by
  have hb := Tammes15.ebase_mem_Ioo d y hd hy
  have h := Tammes15.Contractors.fanC_antitoneOn hd ⟨hb.1, hb.2⟩ ⟨hd.1, by linarith [Real.pi_gt_three]⟩ hp hq hF
  intro a ha b hb' hab
  have := h ha hb' hab
  have e0 : ∀ u v, pentOut 0 d u v = bangle d u + gam d (ebase d u) (ebase d v) + bangle d v := fun u v => by
    simp [pentOut]
  simp only [e0]
  simp only at this
  linarith

theorem pentOut0_antitoneOn_y {d x p q : ℝ} (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x ≤ π) (hp : 0 < p)
    (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta d (ebase d u) (ebase d x) → eta d (ebase d u) (ebase d x) < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam (ebase d x) (ebase d u) d) * cos (u / 2)) :
    AntitoneOn (fun u => pentOut 0 d x u) (Set.Icc p q) := by
  have hb := Tammes15.ebase_mem_Ioo d x hd hx
  have h := Tammes15.Contractors.fanC_antitoneOn hd ⟨hb.1, hb.2⟩ ⟨hd.1, by linarith [Real.pi_gt_three]⟩ hp hq hF
  intro a ha b hb' hab
  have := h ha hb' hab
  have e0 : ∀ u v, pentOut 0 d u v = bangle d u + gam d (ebase d u) (ebase d v) + bangle d v := fun u v => by
    simp [pentOut]
  simp only [e0, gam_swap d (ebase d x)]
  simp only at this
  linarith

theorem pentOut1_antitoneOn_x {d y p q : ℝ} (hd : 0 < d ∧ d < π / 2) (hy : 0 < y ∧ y ≤ π) (hp : 0 < p)
    (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta (ebase d y) (ebase d u) d → eta (ebase d y) (ebase d u) d < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam d (ebase d u) (ebase d y)) * cos (u / 2)) :
    AntitoneOn (fun u => pentOut 1 d u y) (Set.Icc p q) := by
  have hb := Tammes15.ebase_mem_Ioo d y hd hy
  have h := Tammes15.Contractors.fanC_antitoneOn hd ⟨hd.1, by linarith [Real.pi_gt_three]⟩ ⟨hb.1, hb.2⟩ hp hq hF
  intro a ha b hb' hab
  have := h ha hb' hab
  have e1 : ∀ u v, pentOut 1 d u v = bangle d u + gam (ebase d v) (ebase d u) d := fun u v => by
    simp [pentOut]
  simp only [e1]
  simpa using this

theorem ebase_mono {d u v : ℝ} (hd : 0 < d ∧ d < π / 2) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ π) :
    ebase d u ≤ ebase d v := by
  unfold ebase
  have hsd : 0 ≤ sin d := Real.sin_nonneg_of_nonneg_of_le_pi hd.1.le (by linarith [Real.pi_pos])
  have hs : sin (u / 2) ≤ sin (v / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  have := Real.arcsin_le_arcsin (mul_le_mul_of_nonneg_left hs hsd)
  linarith

theorem gam_mono_g {g1 g2 e f : ℝ} (he : 0 < e ∧ e < π) (hf : 0 < f ∧ f < π) (h0 : 0 ≤ g1) (h12 : g1 ≤ g2)
    (h2 : g2 ≤ π) : gam g1 e f ≤ gam g2 e f :=
  Real.arccos_le_arccos (eta_anti_g g1 g2 e f he hf h0 h12 h2)

theorem pentOut1_mono_y {d x y1 y2 : ℝ} (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x ≤ π) (hy1 : 0 < y1)
    (h12 : y1 ≤ y2) (hy2 : y2 ≤ π) : pentOut 1 d x y1 ≤ pentOut 1 d x y2 := by
  have e1 : ∀ u v, pentOut 1 d u v = bangle d u + gam (ebase d v) (ebase d u) d := fun u v => by
    simp [pentOut]
  rw [e1, e1]
  have hb := Tammes15.ebase_mem_Ioo d x hd hx
  have hb1 := Tammes15.ebase_mem_Ioo d y1 hd ⟨hy1, h12.trans hy2⟩
  have hb2 := Tammes15.ebase_mem_Ioo d y2 hd ⟨hy1.trans_le h12, hy2⟩
  have := gam_mono_g (e := ebase d x) (f := d) hb ⟨hd.1, by linarith [Real.pi_gt_three]⟩ hb1.1.le
    (ebase_mono hd hy1.le h12 hy2) hb2.2.le
  linarith

def DirOK (UL UH BXL BXH XL XH DL DH : ℤ) (OUT : ℕ) : Prop :=
  OUT = 1 → ∀ (d : ℝ) (Y : ℝ → ℝ), Enc DL DH d → 0 < d → d < π / 2 → (0 : ℝ) < UL →
    (∀ u : ℝ, Enc UL UH u → 0 < Y u → Y u < π → Enc XL XH (Y u) ∧ Enc BXL BXH (bangle d u + Y u)) →
    ∀ u ∈ Set.Icc ((UL : ℝ) / 2 ^ 28) (min ((UH : ℝ) / 2 ^ 28) π), 0 < Y u → Y u < π →
      0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2)

theorem af_false {lo hi : ℤ} {θ : ℝ} (h : Enc lo hi θ) : AF false lo hi θ := h

theorem fan_sign_of_dir {UL UH BXL BXH XL XH DL DH : ℤ} {OUT : ℕ} (hdir : DirOK UL UH BXL BXH XL XH DL DH OUT)
    (h1 : OUT = 1) {d : ℝ} (hd : Enc DL DH d) (hd0 : 0 < d) (hd1 : d < π / 2) (hUL : (0 : ℝ) < UL) (Z : ℝ → ℝ)
    (hZ : ∀ u, Enc UL UH u → Enc XL XH (arccos (Z u)) ∧ Enc BXL BXH (bangle d u + arccos (Z u))) :
    ∀ u ∈ Set.Icc ((UL : ℝ) / 2 ^ 28) (min ((UH : ℝ) / 2 ^ 28) π),
      0 ≤ cos d * sin (u / 2) + cot (arccos (Z u)) * cos (u / 2) := by
  intro u hu
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1
  refine fan_sign_of_open d u (Z u) ⟨hd0, hd1⟩ ⟨hu0, hu.2.trans (min_le_right _ _)⟩ (fun h0 h1' => ?_)
  exact hdir h1 d (fun u => arccos (Z u)) hd hd0 hd1 hUL (fun u hu _ _ => hZ u hu) u hu h0 h1'

theorem lane_box {F0 F1 F2 F3 : ℕ} (hD : InDom F0 F1 F2 F3) {D0 D1 X0 X1 Y0 Y1 : ℤ}
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) :
    (∀ d : ℝ, Enc D0 D1 d → 0 < d ∧ d < π / 2) ∧ (0 : ℝ) < X0 ∧ (0 : ℝ) < Y0 ∧
      (∀ u : ℝ, Enc X0 X1 u → 0 < u ∧ u < 2 * π) ∧ (∀ u : ℝ, Enc Y0 Y1 u → 0 < u ∧ u < 2 * π) := by
  obtain ⟨-, -, -, -, h0, h1, h2, h3, h4, h5⟩ := hD
  have e0 := div_fld hD0
  have e1 := div_fld hD1
  have e2 := div_fld hX0
  have e3 := div_fld hX1
  have e4 := div_fld hY0
  have e5 := div_fld hY1
  have hpi := Real.pi_gt_three
  have hS : (0 : ℝ) < 2 ^ 28 := by norm_num
  refine ⟨fun d hd => ?_, ?_, ?_, fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨a, b⟩ := mem_of_enc hd
    constructor <;> nlinarith
  · have : (0 : ℝ) < (X0 : ℝ) / 2 ^ 28 := by rw [e2]; linarith
    exact (div_pos_iff_of_pos_right hS).1 this
  · have : (0 : ℝ) < (Y0 : ℝ) / 2 ^ 28 := by rw [e4]; linarith
    exact (div_pos_iff_of_pos_right hS).1 this
  · obtain ⟨a, b⟩ := mem_of_enc hu
    constructor <;> nlinarith
  · obtain ⟨a, b⟩ := mem_of_enc hu
    constructor <;> nlinarith

end D3Prog.L2B
