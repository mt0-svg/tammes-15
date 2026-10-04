import Tammes15.D3Trig.HexLink
import Tammes15.D3Prog.L2.Kinds

open Real

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel
open D3Prog.L2 (Enc AF DirOK)

theorem hexOut_mono_z {d x y z w : ℝ} (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x ≤ π) (hy : 0 < y ∧ y ≤ π)
    (hz : 0 < z ∧ z ≤ π) (hw : 0 < w ∧ w ≤ π) (h : z ≤ w) : hexOut d x y z ≤ hexOut d x y w := by
  have ex := ebase_mem_Ioo d x hd hx
  have ey := ebase_mem_Ioo d y hd hy
  have hm := Tammes15.Contractors.fanOpp_monotoneOn hd ⟨ex.1, ex.2⟩ ⟨ey.1, ey.2⟩ hz hw h
  simp only at hm
  unfold hexOut
  linarith

theorem hexOut_antitoneOn_x {d y z p q : ℝ} (hd : 0 < d ∧ d < π / 2) (hy : 0 < y ∧ y ≤ π) (hz : 0 < z ∧ z ≤ π)
    (hp : 0 < p) (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta (ebase d z) (ebase d u) (ebase d y) →
      eta (ebase d z) (ebase d u) (ebase d y) < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam (ebase d y) (ebase d u) (ebase d z)) * cos (u / 2)) :
    AntitoneOn (fun u => hexOut d u y z) (Set.Icc p q) := by
  have eb := ebase_mem_Ioo d y hd hy
  have ec := ebase_mem_Ioo d z hd hz
  have h := Tammes15.Contractors.fanC_antitoneOn hd ⟨eb.1, eb.2⟩ ⟨ec.1, ec.2⟩ hp hq hF
  intro a ha b hb hab
  have := h ha hb hab
  simp only at this
  simp only [hexOut]
  linarith

theorem hexOut_antitoneOn_y {d x z p q : ℝ} (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x ≤ π) (hz : 0 < z ∧ z ≤ π)
    (hp : 0 < p) (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta (ebase d z) (ebase d u) (ebase d x) →
      eta (ebase d z) (ebase d u) (ebase d x) < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam (ebase d x) (ebase d u) (ebase d z)) * cos (u / 2)) :
    AntitoneOn (fun u => hexOut d x u z) (Set.Icc p q) := by
  have eb := ebase_mem_Ioo d x hd hx
  have ec := ebase_mem_Ioo d z hd hz
  have h := Tammes15.Contractors.fanC_antitoneOn hd ⟨eb.1, eb.2⟩ ⟨ec.1, ec.2⟩ hp hq hF
  intro a ha b hb hab
  have := h ha hb hab
  simp only at this
  simp only [hexOut, D3Prog.L2B.gam_swap (ebase d z) (ebase d x)]
  linarith

theorem KH_hex_eval (G : Prop) (XL XH YL YH ZL ZH DL DH : ℤ)
    (EXL EXH BXL BXH EYL EYH BYL BYH EZL EZH GaL GaH TL TH OL OH : ℤ)
    (hex : G → ∀ d u : ℝ, Enc DL DH d → Enc XL XH u → AF true EXL EXH (ebase d u))
    (hbx : G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc XL XH u → 0 < u → u < 2 * π →
      Enc BXL BXH (bangle d u))
    (hey : G → ∀ d u : ℝ, Enc DL DH d → Enc YL YH u → AF true EYL EYH (ebase d u))
    (hby : G → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc DL DH d → Enc YL YH u → 0 < u → u < 2 * π →
      Enc BYL BYH (bangle d u))
    (hez : G → ∀ d u : ℝ, Enc DL DH d → Enc ZL ZH u → AF true EZL EZH (ebase d u))
    (hg : G → ∀ θg θe θf : ℝ, AF true EZL EZH θg → AF true EXL EXH θe → AF true EYL EYH θf →
      Enc GaL GaH (gam θg θe θf))
    (ht : ∀ r s : ℝ, Enc BXL BXH r → Enc GaL GaH s → Enc TL TH (r + s))
    (ho : ∀ r s : ℝ, Enc TL TH r → Enc BYL BYH s → Enc OL OH (r + s)) :
    G → ∀ d x y z : ℝ, Enc DL DH d → Enc XL XH x → Enc YL YH y → Enc ZL ZH z → 0 < d → d < π / 2 → 0 < x →
      x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (hexOut d x y z) := by
  intro hG d x y z hd hx hy hz hd0 hd1 hx0 hx1 hy0 hy1
  have hgE := hg hG _ _ _ (hez hG d z hd hz) (hex hG d x hd hx) (hey hG d y hd hy)
  exact ho _ _ (ht _ _ (hbx hG d x hd0 hd1 hd hx hx0 hx1) hgE) (hby hG d y hd0 hd1 hd hy hy0 hy1)

theorem divH {F s : ℕ} {V : ℤ} (hV : V = ((F / 2 ^ s % 2 ^ 32 * 16 : ℕ) : ℤ)) : (V : ℝ) / 2 ^ 28 = fld F s :=
  D3Prog.L2B.div_fld hV

theorem encH {F : ℕ} {V W : ℤ} (hV : V = ((F / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hW : W = ((F / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) {x : ℝ} (h1 : fld F 0 ≤ x) (h2 : x ≤ fld F 32) : Enc V W x :=
  D3Prog.L2B.enc_fld hV hW h1 h2

theorem laneH_box {F0 F1 F2 F3 : ℕ} (hD : InDomH F0 F1 F2 F3) {D0 D1 X0 Y0 T : ℤ}
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) :
    (∀ d : ℝ, Enc D0 D1 d → 0 < d ∧ d < π / 2) ∧ (1 : ℝ) < (X0 : ℝ) / 2 ^ 28 ∧ (1 : ℝ) < (Y0 : ℝ) / 2 ^ 28 ∧
      (1 : ℝ) < (T : ℝ) / 2 ^ 28 ∧ fld F1 32 ≤ 3.2 ∧ fld F2 32 ≤ 3.2 := by
  obtain ⟨-, -, -, -, h0, h1, h2, h3, h4, h5, h6, -⟩ := hD
  have e0 := divH hD0
  have e1 := divH hD1
  have e2 := divH hX0
  have e4 := divH hY0
  have e6 := divH hT
  have h0' : (0.9 : ℝ) ≤ fld F0 0 := h0
  have h1' : fld F0 32 ≤ 1 := h1
  have h2' : (1.1 : ℝ) ≤ fld F1 0 := h2
  have h4' : (1.1 : ℝ) ≤ fld F2 0 := h4
  have h6' : (1.1 : ℝ) ≤ fld F3 32 := h6
  refine ⟨fun d hd => ?_, by linarith, by linarith, by linarith, h3, h5⟩
  obtain ⟨l, u⟩ := D3Prog.L2B.mem_of_enc hd
  constructor <;> linarith [pi_gt_three]

theorem claimH_of_check (hi : Bool) {F3 : ℕ} {C : ℤ} (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (side : ℕ)
    (OL OH : ℤ) (lo_ok hi_ok cl : ℕ) (hside : side = 1 ↔ hi = true) (hlo_ok : lo_ok = 1 ↔ C ≤ OL)
    (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok) (hck : True → cl = 1) (r : ℝ)
    (hr : Enc OL OH r) : Claim hi (fld F3 0) r := by
  have h := D3Prog.L2B.claim_of_check hi side C OL OH lo_ok hi_ok cl hside hlo_ok hhi_ok hcl hck r hr
  have e : (C : ℝ) / 2 ^ 28 = fld F3 0 := divH hC
  rw [e] at h
  exact h

theorem zcorner_lo {F3 : ℕ} {T K ZL ZH : ℤ} (side : ℕ) (hside : ¬side = 1)
    (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hT1 : (1 : ℝ) < (T : ℝ) / 2 ^ 28) (hK : K = 843314857)
    (hz : ∀ t : ℝ, Enc T K t → t ≤ π → ∃ w : ℝ, Enc ZL ZH w ∧ (T : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((K : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t))
    (z : ℝ) (hzt : fld F3 32 ≤ z) (hzpi : z < π) :
    ∃ w : ℝ, Enc ZL ZH w ∧ 1 < w ∧ w ≤ π ∧ w ≤ z := by
  have e := divH hT
  have hzE : Enc T K z := by
    refine D3Prog.L2B.enc_of_mem (by rw [e]; exact hzt) ?_
    rw [hK, le_div_iff₀ (by norm_num)]
    have := D3Prog.L2B.pi_hi_gt
    push_cast
    nlinarith
  obtain ⟨w, hwE, hwl, hwh, -, hw0⟩ := hz z hzE hzpi.le
  exact ⟨w, hwE, by linarith, hwh.trans (min_le_right _ _), hw0 hside⟩

theorem zcorner_hi {F3 : ℕ} {T K ZL ZH : ℤ} (side : ℕ) (hside : side = 1)
    (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hK : K = 0)
    (hz : ∀ t : ℝ, Enc K T t → t ≤ π → ∃ w : ℝ, Enc ZL ZH w ∧ (K : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((T : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t))
    (z : ℝ) (hz0 : 0 < z) (hzt : z ≤ fld F3 32) (hzpi : z < π) :
    ∃ w : ℝ, Enc ZL ZH w ∧ z ≤ w ∧ w ≤ π := by
  have e := divH hT
  have hzE : Enc K T z := by
    refine D3Prog.L2B.enc_of_mem ?_ (by rw [e]; exact hzt)
    rw [hK]
    push_cast
    linarith
  obtain ⟨w, hwE, -, hwh, hw1, -⟩ := hz z hzE hzpi.le
  exact ⟨w, hwE, hw1 hside, hwh.trans (min_le_right _ _)⟩

theorem hexN_core (hi : Bool) {F0 F1 F2 F3 : ℕ} (hD : InDomH F0 F1 F2 F3) {D0 D1 X0 X1 Y0 Y1 C T ZL ZH OL OH : ℤ}
    {side : ℕ} {lo_ok hi_ok cl : ℕ}
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hside : side = 1 ↔ hi = true)
    (hout : True → ∀ d x y z : ℝ, Enc D0 D1 d → Enc X0 X1 x → Enc Y0 Y1 y → Enc ZL ZH z → 0 < d → d < π / 2 →
      0 < x → x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (hexOut d x y z))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1)
    (hw : ∀ z : ℝ, z < π → (if hi then 0 < z ∧ z ≤ fld F3 32 else fld F3 32 ≤ z) →
      ∃ w : ℝ, Enc ZL ZH w ∧ 0 < z ∧ 0 < w ∧ w ≤ π ∧ (hi = true → z ≤ w) ∧ (hi = false → w ≤ z)) :
    LaneClaimH hi F0 F1 F2 F3 := by
  obtain ⟨hdbox, hx1, hy1, -, -, -⟩ := laneH_box hD hD0 hD1 hX0 hY0 hT
  intro d x y z hdl hdh hxl hxh hyl hyh hxpi hypi hzpi hzt
  have hdE : Enc D0 D1 d := encH hD0 hD1 hdl hdh
  have hxE : Enc X0 X1 x := encH hX0 hX1 hxl hxh
  have hyE : Enc Y0 Y1 y := encH hY0 hY1 hyl hyh
  have hd := hdbox d hdE
  have hx0 : 1 < x := hx1.trans_le (D3Prog.L2B.mem_of_enc hxE).1
  have hy0 : 1 < y := hy1.trans_le (D3Prog.L2B.mem_of_enc hyE).1
  obtain ⟨w, hwE, hz0, hw0, hwpi, hwhi, hwlo⟩ := hw z hzpi hzt
  have hc := claimH_of_check hi hC side OL OH lo_ok hi_ok cl hside hlo_ok hhi_ok hcl hck _
    (hout trivial d x y w hdE hxE hyE hwE hd.1 hd.2 (by linarith) (by linarith [pi_gt_three])
      (by linarith) (by linarith [pi_gt_three]))
  have hxI : 0 < x ∧ x ≤ π := ⟨by linarith, hxpi.le⟩
  have hyI : 0 < y ∧ y ≤ π := ⟨by linarith, hypi.le⟩
  unfold Claim at hc ⊢
  cases hi with
  | false =>
    have := hexOut_mono_z hd hxI hyI ⟨hw0, hwpi⟩ ⟨hz0, hzpi.le⟩ (hwlo rfl)
    simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    linarith
  | true =>
    have := hexOut_mono_z hd hxI hyI ⟨hz0, hzpi.le⟩ ⟨hw0, hwpi⟩ (hwhi rfl)
    simp only [↓reduceIte] at hc ⊢
    linarith

theorem THNL (F0 F1 F2 F3 : ℕ) (hD : InDomH F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C T : ℤ) (side : ℕ)
    (K ZL ZH OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hside : ¬side = 1) (hK : K = 843314857)
    (hz : ∀ t : ℝ, Enc T K t → t ≤ π → ∃ w : ℝ, Enc ZL ZH w ∧ (T : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((K : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t))
    (hout : True → ∀ d x y z : ℝ, Enc D0 D1 d → Enc X0 X1 x → Enc Y0 Y1 y → Enc ZL ZH z → 0 < d → d < π / 2 →
      0 < x → x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (hexOut d x y z))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaimH false F0 F1 F2 F3 := by
  obtain ⟨-, -, -, hT1, -, -⟩ := laneH_box hD hD0 hD1 hX0 hY0 hT
  refine hexN_core false hD hD0 hD1 hX0 hX1 hY0 hY1 hC hT
    ⟨fun h => absurd h hside, fun h => absurd h Bool.false_ne_true⟩ hout hlo_ok hhi_ok hcl hck ?_
  intro z hzpi hzt
  simp only [Bool.false_eq_true, ↓reduceIte] at hzt
  obtain ⟨w, hwE, hw1, hwpi, hwz⟩ := zcorner_lo side hside hT hT1 hK hz z hzt hzpi
  exact ⟨w, hwE, by linarith, by linarith, hwpi, fun h => absurd h Bool.false_ne_true, fun _ => hwz⟩

theorem THNH (F0 F1 F2 F3 : ℕ) (hD : InDomH F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C T : ℤ) (side : ℕ)
    (K ZL ZH OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hside : side = 1) (hK : K = 0)
    (hz : ∀ t : ℝ, Enc K T t → t ≤ π → ∃ w : ℝ, Enc ZL ZH w ∧ (K : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((T : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t))
    (hout : True → ∀ d x y z : ℝ, Enc D0 D1 d → Enc X0 X1 x → Enc Y0 Y1 y → Enc ZL ZH z → 0 < d → d < π / 2 →
      0 < x → x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (hexOut d x y z))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaimH true F0 F1 F2 F3 := by
  refine hexN_core true hD hD0 hD1 hX0 hX1 hY0 hY1 hC hT ⟨fun _ => rfl, fun _ => hside⟩ hout hlo_ok hhi_ok hcl
    hck ?_
  intro z hzpi hzt
  simp only [↓reduceIte] at hzt
  obtain ⟨w, hwE, hzw, hwpi⟩ := zcorner_hi side hside hT hK hz z hzt.1 hzt.2 hzpi
  exact ⟨w, hwE, hzt.1, by linarith [hzt.1], hwpi, fun _ => hzw, fun h => absurd h (by decide)⟩

theorem hexM_core (hi : Bool) {F0 F1 F2 F3 : ℕ} (hD : InDomH F0 F1 F2 F3) {D0 D1 X0 X1 Y0 Y1 C T : ℤ}
    {side : ℕ} {ZL ZH EXL EXH BXL BXH EYL EYH BYL BYH EZL EZH GXL GXH GYL GYH BX0L BX0H BX1L BX1H : ℤ}
    {d0 d1 : ℕ} {P0L P0H P1L P1H OL OH : ℤ} {lo_ok hi_ok cl : ℕ}
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hside : side = 1 ↔ hi = true)
    (hex : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EXL EXH (ebase d u))
    (hbx : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc BXL BXH (bangle d u))
    (hey : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true EYL EYH (ebase d u))
    (hby : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc Y0 Y1 u → 0 < u → u < 2 * π →
      Enc BYL BYH (bangle d u))
    (hez : True → ∀ d u : ℝ, Enc D0 D1 d → Enc ZL ZH u → AF true EZL EZH (ebase d u))
    (hgx : True → ∀ θg θe θf : ℝ, AF true EYL EYH θg → AF true EXL EXH θe → AF true EZL EZH θf →
      Enc GXL GXH (gam θg θe θf))
    (hgy : True → ∀ θg θe θf : ℝ, AF true EXL EXH θg → AF true EYL EYH θe → AF true EZL EZH θf →
      Enc GYL GYH (gam θg θe θf))
    (hbx0 : ∀ r s : ℝ, Enc BXL BXH r → Enc GXL GXH s → Enc BX0L BX0H (r + s))
    (hbx1 : ∀ r s : ℝ, Enc BYL BYH r → Enc GYL GYH s → Enc BX1L BX1H (r + s))
    (hd0 : True → DirOK X0 X1 BX0L BX0H GXL GXH D0 D1 d0)
    (hd1 : True → DirOK Y0 Y1 BX1L BX1H GYL GYH D0 D1 d1)
    (hx0 : ∀ t : ℝ, Enc X0 X1 t → t ≤ π → ∃ w : ℝ, Enc P0L P0H w ∧ (X0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((X1 : ℝ) / 2 ^ 28) π ∧ (d0 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d0 = 1 → w = t))
    (hx1 : ∀ t : ℝ, Enc Y0 Y1 t → t ≤ π → ∃ w : ℝ, Enc P1L P1H w ∧ (Y0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((Y1 : ℝ) / 2 ^ 28) π ∧ (d1 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d1 = 1 → w = t))
    (hout : True → ∀ d x y z : ℝ, Enc D0 D1 d → Enc P0L P0H x → Enc P1L P1H y → Enc ZL ZH z → 0 < d →
      d < π / 2 → 0 < x → x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (hexOut d x y z))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1)
    (hw : ∀ z : ℝ, z < π → (if hi then 0 < z ∧ z ≤ fld F3 32 else fld F3 32 ≤ z) →
      ∃ w : ℝ, Enc ZL ZH w ∧ 0 < z ∧ 0 < w ∧ w ≤ π ∧ (hi = true → z ≤ w) ∧ (hi = false → w ≤ z)) :
    LaneClaimH hi F0 F1 F2 F3 := by
  obtain ⟨hdbox, hX1p, hY1p, -, hX3, hY3⟩ := laneH_box hD hD0 hD1 hX0 hY0 hT
  have eX1 := divH hX1
  have eY1 := divH hY1
  have hpi3 := pi_gt_three
  have hX0p : (0 : ℝ) < X0 := by
    have : (0 : ℝ) < (X0 : ℝ) / 2 ^ 28 := by linarith
    have h28 : (0 : ℝ) < 2 ^ 28 := by norm_num
    have := mul_pos this h28
    rwa [div_mul_cancel₀ _ h28.ne'] at this
  have hY0p : (0 : ℝ) < Y0 := by
    have : (0 : ℝ) < (Y0 : ℝ) / 2 ^ 28 := by linarith
    have h28 : (0 : ℝ) < 2 ^ 28 := by norm_num
    have := mul_pos this h28
    rwa [div_mul_cancel₀ _ h28.ne'] at this
  have boxX : ∀ u : ℝ, Enc X0 X1 u → 0 < u ∧ u < 2 * π := fun u hu => by
    obtain ⟨l, h⟩ := D3Prog.L2B.mem_of_enc hu
    constructor <;> linarith
  have boxY : ∀ u : ℝ, Enc Y0 Y1 u → 0 < u ∧ u < 2 * π := fun u hu => by
    obtain ⟨l, h⟩ := D3Prog.L2B.mem_of_enc hu
    constructor <;> linarith
  intro d x y z hdl hdh hxl hxh hyl hyh hxpi hypi hzpi hzt
  have hdE : Enc D0 D1 d := encH hD0 hD1 hdl hdh
  have hxE : Enc X0 X1 x := encH hX0 hX1 hxl hxh
  have hyE : Enc Y0 Y1 y := encH hY0 hY1 hyl hyh
  have hd := hdbox d hdE
  obtain ⟨wz, hwzE, hz0, hwz0, hwzpi, hwzhi, hwzlo⟩ := hw z hzpi hzt
  obtain ⟨w0, hw0E, hw0l, hw0h, hw0d, hw0n⟩ := hx0 x hxE hxpi.le
  obtain ⟨w1, hw1E, hw1l, hw1h, hw1d, hw1n⟩ := hx1 y hyE hypi.le
  have hw0X : Enc X0 X1 w0 := D3Prog.L2B.enc_of_mem hw0l (hw0h.trans (min_le_left _ _))
  have hw1Y : Enc Y0 Y1 w1 := D3Prog.L2B.enc_of_mem hw1l (hw1h.trans (min_le_left _ _))
  have hw0pi : w0 ≤ π := hw0h.trans (min_le_right _ _)
  have hw1pi : w1 ≤ π := hw1h.trans (min_le_right _ _)
  have hw0b := boxX w0 hw0X
  have hw1b := boxY w1 hw1Y
  have hxb := boxX x hxE
  have hyb := boxY y hyE
  have hxI : x ∈ Set.Icc ((X0 : ℝ) / 2 ^ 28) (min ((X1 : ℝ) / 2 ^ 28) π) :=
    ⟨(D3Prog.L2B.mem_of_enc hxE).1, le_min (D3Prog.L2B.mem_of_enc hxE).2 hxpi.le⟩
  have hyI : y ∈ Set.Icc ((Y0 : ℝ) / 2 ^ 28) (min ((Y1 : ℝ) / 2 ^ 28) π) :=
    ⟨(D3Prog.L2B.mem_of_enc hyE).1, le_min (D3Prog.L2B.mem_of_enc hyE).2 hypi.le⟩
  have hw0I : w0 ∈ Set.Icc ((X0 : ℝ) / 2 ^ 28) (min ((X1 : ℝ) / 2 ^ 28) π) := ⟨hw0l, hw0h⟩
  have hw1I : w1 ∈ Set.Icc ((Y0 : ℝ) / 2 ^ 28) (min ((Y1 : ℝ) / 2 ^ 28) π) := ⟨hw1l, hw1h⟩
  have hp0 : (0 : ℝ) < (X0 : ℝ) / 2 ^ 28 := by positivity
  have hp1 : (0 : ℝ) < (Y0 : ℝ) / 2 ^ 28 := by positivity
  have hc := claimH_of_check hi hC side OL OH lo_ok hi_ok cl hside hlo_ok hhi_ok hcl hck _
    (hout trivial d w0 w1 wz hdE hw0E hw1E hwzE hd.1 hd.2 hw0b.1 hw0b.2 hw1b.1 hw1b.2)
  have stepX : (side = 1 → hexOut d x y wz ≤ hexOut d w0 y wz) ∧
      (¬side = 1 → hexOut d w0 y wz ≤ hexOut d x y wz) := by
    by_cases h1 : d0 = 1
    · have hanti := hexOut_antitoneOn_x (y := y) (z := wz) (p := (X0 : ℝ) / 2 ^ 28)
        (q := min ((X1 : ℝ) / 2 ^ 28) π) hd ⟨hyb.1, hypi.le⟩ ⟨hwz0, hwzpi⟩ hp0 (min_le_right _ _)
        (fun u hu _ _ => D3Prog.L2B.fan_sign_of_dir (hd0 trivial) h1 hdE hd.1 hd.2 hX0p
          (fun u => eta (ebase d y) (ebase d u) (ebase d wz))
          (fun u hu =>
            have hg := hgx trivial (ebase d y) (ebase d u) (ebase d wz) (hey trivial d y hdE hyE)
              (hex trivial d u hdE hu) (hez trivial d wz hdE hwzE)
            ⟨hg, hbx0 _ _ (hbx trivial d u hd.1 hd.2 hdE hu (boxX u hu).1 (boxX u hu).2) hg⟩) u hu)
      obtain ⟨hs1, hs0⟩ := hw0d h1
      exact ⟨fun hs => hanti hw0I hxI (hs1 hs), fun hs => hanti hxI hw0I (hs0 hs)⟩
    · rw [hw0n h1]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  have stepY : (side = 1 → hexOut d w0 y wz ≤ hexOut d w0 w1 wz) ∧
      (¬side = 1 → hexOut d w0 w1 wz ≤ hexOut d w0 y wz) := by
    by_cases h1 : d1 = 1
    · have hanti := hexOut_antitoneOn_y (x := w0) (z := wz) (p := (Y0 : ℝ) / 2 ^ 28)
        (q := min ((Y1 : ℝ) / 2 ^ 28) π) hd ⟨hw0b.1, hw0pi⟩ ⟨hwz0, hwzpi⟩ hp1 (min_le_right _ _)
        (fun u hu _ _ => D3Prog.L2B.fan_sign_of_dir (hd1 trivial) h1 hdE hd.1 hd.2 hY0p
          (fun u => eta (ebase d w0) (ebase d u) (ebase d wz))
          (fun u hu =>
            have hg := hgy trivial (ebase d w0) (ebase d u) (ebase d wz) (hex trivial d w0 hdE hw0X)
              (hey trivial d u hdE hu) (hez trivial d wz hdE hwzE)
            ⟨hg, hbx1 _ _ (hby trivial d u hd.1 hd.2 hdE hu (boxY u hu).1 (boxY u hu).2) hg⟩) u hu)
      obtain ⟨hs1, hs0⟩ := hw1d h1
      exact ⟨fun hs => hanti hw1I hyI (hs1 hs), fun hs => hanti hyI hw1I (hs0 hs)⟩
    · rw [hw1n h1]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  have hxI' : 0 < x ∧ x ≤ π := ⟨hxb.1, hxpi.le⟩
  have hyI' : 0 < y ∧ y ≤ π := ⟨hyb.1, hypi.le⟩
  unfold Claim at hc ⊢
  cases hi with
  | false =>
    have hs : ¬side = 1 := fun h => Bool.false_ne_true (hside.1 h)
    have := hexOut_mono_z hd hxI' hyI' ⟨hwz0, hwzpi⟩ ⟨hz0, hzpi.le⟩ (hwzlo rfl)
    simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    linarith [stepX.2 hs, stepY.2 hs]
  | true =>
    have hs : side = 1 := hside.2 rfl
    have := hexOut_mono_z hd hxI' hyI' ⟨hz0, hzpi.le⟩ ⟨hwz0, hwzpi⟩ (hwzhi rfl)
    simp only [↓reduceIte] at hc ⊢
    linarith [stepX.1 hs, stepY.1 hs]

theorem THML (F0 F1 F2 F3 : ℕ) (hD : InDomH F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C T : ℤ) (side : ℕ)
    (K ZL ZH EXL EXH BXL BXH EYL EYH BYL BYH EZL EZH GXL GXH GYL GYH BX0L BX0H BX1L BX1H : ℤ) (d0 d1 : ℕ)
    (P0L P0H P1L P1H OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hside : ¬side = 1) (hK : K = 843314857)
    (hz : ∀ t : ℝ, Enc T K t → t ≤ π → ∃ w : ℝ, Enc ZL ZH w ∧ (T : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((K : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t))
    (hex : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EXL EXH (ebase d u))
    (hbx : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc BXL BXH (bangle d u))
    (hey : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true EYL EYH (ebase d u))
    (hby : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc Y0 Y1 u → 0 < u → u < 2 * π →
      Enc BYL BYH (bangle d u))
    (hez : True → ∀ d u : ℝ, Enc D0 D1 d → Enc ZL ZH u → AF true EZL EZH (ebase d u))
    (hgx : True → ∀ θg θe θf : ℝ, AF true EYL EYH θg → AF true EXL EXH θe → AF true EZL EZH θf →
      Enc GXL GXH (gam θg θe θf))
    (hgy : True → ∀ θg θe θf : ℝ, AF true EXL EXH θg → AF true EYL EYH θe → AF true EZL EZH θf →
      Enc GYL GYH (gam θg θe θf))
    (hbx0 : ∀ r s : ℝ, Enc BXL BXH r → Enc GXL GXH s → Enc BX0L BX0H (r + s))
    (hbx1 : ∀ r s : ℝ, Enc BYL BYH r → Enc GYL GYH s → Enc BX1L BX1H (r + s))
    (hd0 : True → DirOK X0 X1 BX0L BX0H GXL GXH D0 D1 d0)
    (hd1 : True → DirOK Y0 Y1 BX1L BX1H GYL GYH D0 D1 d1)
    (hx0 : ∀ t : ℝ, Enc X0 X1 t → t ≤ π → ∃ w : ℝ, Enc P0L P0H w ∧ (X0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((X1 : ℝ) / 2 ^ 28) π ∧ (d0 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d0 = 1 → w = t))
    (hx1 : ∀ t : ℝ, Enc Y0 Y1 t → t ≤ π → ∃ w : ℝ, Enc P1L P1H w ∧ (Y0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((Y1 : ℝ) / 2 ^ 28) π ∧ (d1 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d1 = 1 → w = t))
    (hout : True → ∀ d x y z : ℝ, Enc D0 D1 d → Enc P0L P0H x → Enc P1L P1H y → Enc ZL ZH z → 0 < d →
      d < π / 2 → 0 < x → x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (hexOut d x y z))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaimH false F0 F1 F2 F3 := by
  obtain ⟨-, -, -, hT1, -, -⟩ := laneH_box hD hD0 hD1 hX0 hY0 hT
  refine hexM_core false hD hD0 hD1 hX0 hX1 hY0 hY1 hC hT
    ⟨fun h => absurd h hside, fun h => absurd h Bool.false_ne_true⟩ hex hbx hey hby hez hgx hgy hbx0 hbx1 hd0 hd1
    hx0 hx1 hout hlo_ok hhi_ok hcl hck ?_
  intro z hzpi hzt
  simp only [Bool.false_eq_true, ↓reduceIte] at hzt
  obtain ⟨w, hwE, hw1, hwpi, hwz⟩ := zcorner_lo side hside hT hT1 hK hz z hzt hzpi
  exact ⟨w, hwE, by linarith, by linarith, hwpi, fun h => absurd h Bool.false_ne_true, fun _ => hwz⟩

theorem THMH (F0 F1 F2 F3 : ℕ) (hD : InDomH F0 F1 F2 F3) (D0 D1 X0 X1 Y0 Y1 C T : ℤ) (side : ℕ)
    (K ZL ZH EXL EXH BXL BXH EYL EYH BYL BYH EZL EZH GXL GXH GYL GYH BX0L BX0H BX1L BX1H : ℤ) (d0 d1 : ℕ)
    (P0L P0H P1L P1H OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hT : T = ((F3 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hside : side = 1) (hK : K = 0)
    (hz : ∀ t : ℝ, Enc K T t → t ≤ π → ∃ w : ℝ, Enc ZL ZH w ∧ (K : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((T : ℝ) / 2 ^ 28) π ∧ (side = 1 → t ≤ w) ∧ (¬side = 1 → w ≤ t))
    (hex : True → ∀ d u : ℝ, Enc D0 D1 d → Enc X0 X1 u → AF true EXL EXH (ebase d u))
    (hbx : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc BXL BXH (bangle d u))
    (hey : True → ∀ d u : ℝ, Enc D0 D1 d → Enc Y0 Y1 u → AF true EYL EYH (ebase d u))
    (hby : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc Y0 Y1 u → 0 < u → u < 2 * π →
      Enc BYL BYH (bangle d u))
    (hez : True → ∀ d u : ℝ, Enc D0 D1 d → Enc ZL ZH u → AF true EZL EZH (ebase d u))
    (hgx : True → ∀ θg θe θf : ℝ, AF true EYL EYH θg → AF true EXL EXH θe → AF true EZL EZH θf →
      Enc GXL GXH (gam θg θe θf))
    (hgy : True → ∀ θg θe θf : ℝ, AF true EXL EXH θg → AF true EYL EYH θe → AF true EZL EZH θf →
      Enc GYL GYH (gam θg θe θf))
    (hbx0 : ∀ r s : ℝ, Enc BXL BXH r → Enc GXL GXH s → Enc BX0L BX0H (r + s))
    (hbx1 : ∀ r s : ℝ, Enc BYL BYH r → Enc GYL GYH s → Enc BX1L BX1H (r + s))
    (hd0 : True → DirOK X0 X1 BX0L BX0H GXL GXH D0 D1 d0)
    (hd1 : True → DirOK Y0 Y1 BX1L BX1H GYL GYH D0 D1 d1)
    (hx0 : ∀ t : ℝ, Enc X0 X1 t → t ≤ π → ∃ w : ℝ, Enc P0L P0H w ∧ (X0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((X1 : ℝ) / 2 ^ 28) π ∧ (d0 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d0 = 1 → w = t))
    (hx1 : ∀ t : ℝ, Enc Y0 Y1 t → t ≤ π → ∃ w : ℝ, Enc P1L P1H w ∧ (Y0 : ℝ) / 2 ^ 28 ≤ w ∧
      w ≤ min ((Y1 : ℝ) / 2 ^ 28) π ∧ (d1 = 1 → (side = 1 → w ≤ t) ∧ (¬side = 1 → t ≤ w)) ∧ (¬d1 = 1 → w = t))
    (hout : True → ∀ d x y z : ℝ, Enc D0 D1 d → Enc P0L P0H x → Enc P1L P1H y → Enc ZL ZH z → 0 < d →
      d < π / 2 → 0 < x → x < 2 * π → 0 < y → y < 2 * π → Enc OL OH (hexOut d x y z))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaimH true F0 F1 F2 F3 := by
  refine hexM_core true hD hD0 hD1 hX0 hX1 hY0 hY1 hC hT ⟨fun _ => rfl, fun _ => hside⟩ hex hbx hey hby hez hgx
    hgy hbx0 hbx1 hd0 hd1 hx0 hx1 hout hlo_ok hhi_ok hcl hck ?_
  intro z hzpi hzt
  simp only [↓reduceIte] at hzt
  obtain ⟨w, hwE, hzw, hwpi⟩ := zcorner_hi side hside hT hK hz z hzt.1 hzt.2 hzpi
  exact ⟨w, hwE, hzt.1, by linarith [hzt.1], hwpi, fun _ => hzw, fun h => absurd h (by decide)⟩

end Tammes15.D3Trig
