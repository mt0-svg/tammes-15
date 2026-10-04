import Tammes15.D3Trig.RhoLink
import Tammes15.D3Prog.L2.Kinds

open Real

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel
open D3Prog.L2 (Enc K1_ix K29_claim bangle_anti)

theorem rho_eq_two_bangle {d x : ℝ} (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x < π) :
    rho d x = 2 * bangle d x := by
  have hc : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith [hd.1], hd.2⟩
  have hs : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  have hc2 : 0 < cos (x / 2) := cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have ht : 0 < cos d * tan (x / 2) := mul_pos hc (by rw [tan_eq_sin_div_cos]; exact div_pos hs hc2)
  have hinv : cos (x / 2) / (cos d * sin (x / 2)) = (cos d * tan (x / 2))⁻¹ := by
    rw [tan_eq_sin_div_cos]; field_simp
  unfold rho bangle
  rw [hinv, arctan_inv_of_pos ht]
  ring

theorem ix_eq {F s : ℕ} {V : ℤ} (h : V = ((F / 2 ^ s % 2 ^ 32 * 16 : ℕ) : ℤ)) : (V : ℝ) = 2 ^ 28 * fld F s :=
  K1_ix F s V h

theorem enc_box {F : ℕ} {V0 V1 : ℤ} (h0 : V0 = ((F / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (h1 : V1 = ((F / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) {r : ℝ} (hr0 : fld F 0 ≤ r) (hr1 : r ≤ fld F 32) :
    Enc V0 V1 r := by
  rw [Enc, ix_eq h0, ix_eq h1]
  constructor <;> nlinarith

theorem enc_pt {F s : ℕ} {V : ℤ} (h : V = ((F / 2 ^ s % 2 ^ 32 * 16 : ℕ) : ℤ)) : Enc V V (fld F s) := by
  rw [Enc, ix_eq h]
  exact ⟨le_rfl, le_rfl⟩

theorem TR (hi : Bool) (F0 F1 F2 F3 : ℕ) (hD : D3Prog.L2.InDom F0 F1 F2 F3) (D0 D1 X0 X1 C : ℤ) (side : ℕ)
    (BL BH OL OH : ℤ) (lo_ok hi_ok cl : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hside : side = 1 ↔ hi = true)
    (hb : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc D0 D1 d → Enc X0 X1 u → 0 < u → u < 2 * π →
      Enc BL BH (bangle d u))
    (ho : ∀ r s : ℝ, Enc BL BH r → Enc BL BH s → Enc OL OH (r + s))
    (hlo_ok : lo_ok = 1 ↔ C ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ C) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hck : True → cl = 1) :
    LaneClaimR 0 hi F0 F1 F2 F3 := by
  intro d x y hd0 hd1 hx0 hx1 _ _ hxpi hy
  obtain ⟨-, -, -, -, h09, h1, h11, -, -, -⟩ := hD
  have h09' : (0.9 : ℝ) ≤ fld F0 0 := h09
  have h1' : fld F0 32 ≤ 1 := h1
  have h11' : (1.1 : ℝ) ≤ fld F1 0 := h11
  have hdpos : 0 < d := by linarith
  have hdlt : d < π / 2 := by linarith [pi_gt_three]
  have hxpos : 0 < x := by linarith
  have hB := hb trivial d x hdpos hdlt (enc_box hD0 hD1 hd0 hd1) (enc_box hX0 hX1 hx0 hx1) hxpos
    (by linarith [pi_pos])
  have hcl' := K29_claim hi side C OL OH lo_ok hi_ok cl hside hlo_ok hhi_ok hcl hck _ (ho _ _ hB hB)
  have hc28 : (C : ℝ) / 2 ^ 28 = fld F3 0 := by rw [ix_eq hC]; field_simp
  simp only [↓reduceIte]
  rw [hy, rho_eq_two_bangle ⟨hdpos, hdlt⟩ ⟨hxpos, hxpi⟩, two_mul, ← hc28]
  exact hcl'

theorem TDL (F0 F1 F2 F3 : ℕ) (hD : D3Prog.L2.InDom F0 F1 F2 F3) (D1 X0 Y0 C : ℤ) (side : ℕ) (BL BH OL OH : ℤ)
    (lo_ok hi_ok cl dok cl2 : ℕ)
    (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX0 : X0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY0 : Y0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hside : side = 1)
    (hb : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc C C d → Enc X0 X0 u → 0 < u → u < 2 * π →
      Enc BL BH (bangle d u))
    (ho : ∀ r s : ℝ, Enc BL BH r → Enc BL BH s → Enc OL OH (r + s))
    (hlo_ok : lo_ok = 1 ↔ Y0 ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ Y0) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hdok : dok = 1 ↔ C ≤ D1) (hand : cl2 = 1 ↔ cl = 1 ∧ dok = 1) (hck : True → cl2 = 1) :
    LaneClaimR 1 false F0 F1 F2 F3 := by
  intro d x y hd0 hd1 hx0 _ hy0 _ hxpi hy
  obtain ⟨-, -, -, -, h09, h1, h11, -, -, -⟩ := hD
  have h09' : (0.9 : ℝ) ≤ fld F0 0 := h09
  have h1' : fld F0 32 ≤ 1 := h1
  have h11' : (1.1 : ℝ) ≤ fld F1 0 := h11
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte]
  show fld F3 0 ≤ d
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hcl1, hdok1⟩ := hand.mp (hck trivial)
  rw [hcl, hside] at hcl1
  simp only [↓reduceIte] at hcl1
  have hOY : (OH : ℝ) ≤ Y0 := by exact_mod_cast hhi_ok.mp hcl1
  have hCD : (C : ℝ) ≤ D1 := by exact_mod_cast hdok.mp hdok1
  rw [ix_eq hC, ix_eq hD1] at hCD
  rw [ix_eq hY0] at hOY
  have hc1 : fld F3 0 ≤ fld F0 32 := by nlinarith
  have hdpos : 0 < d := by linarith
  have hcpos : 0 < fld F3 0 := by linarith
  have hclt : fld F3 0 < π / 2 := by linarith [pi_gt_three]
  have hdlt : d < π / 2 := by linarith
  have hxl : 0 < fld F1 0 := by linarith
  have hxpos : 0 < x := by linarith
  have hB := hb trivial (fld F3 0) (fld F1 0) hcpos hclt (enc_pt hC) (enc_pt hX0) hxl (by linarith [pi_pos])
  have hO := (ho _ _ hB hB).2
  have hmono := rho_strictMonoOn_d x ⟨hxpos, hxpi⟩ ⟨hdpos, hdlt⟩ ⟨hcpos, hclt⟩ hlt
  have hanti := (rho_strictAntiOn_x (fld F3 0) ⟨hcpos, hclt⟩).antitoneOn ⟨hxl, by linarith⟩ ⟨hxpos, hxpi⟩ hx0
  rw [rho_eq_two_bangle ⟨hcpos, hclt⟩ ⟨hxl, by linarith⟩] at hanti
  have : y < fld F2 0 := by
    rw [hy]
    have : 2 ^ 28 * (2 * bangle (fld F3 0) (fld F1 0)) ≤ 2 ^ 28 * fld F2 0 := by linarith
    linarith
  linarith

theorem TDH (F0 F1 F2 F3 : ℕ) (hD : D3Prog.L2.InDom F0 F1 F2 F3) (D0 X1 Y1 C : ℤ) (side : ℕ) (BL BH OL OH : ℤ)
    (lo_ok hi_ok cl dok cl2 : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hX1 : X1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hY1 : Y1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hC : C = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hside : side = 0)
    (hb : True → ∀ d u : ℝ, 0 < d → d < π / 2 → Enc C C d → Enc X1 X1 u → 0 < u → u < 2 * π →
      Enc BL BH (bangle d u))
    (ho : ∀ r s : ℝ, Enc BL BH r → Enc BL BH s → Enc OL OH (r + s))
    (hlo_ok : lo_ok = 1 ↔ Y1 ≤ OL) (hhi_ok : hi_ok = 1 ↔ OH ≤ Y1) (hcl : cl = if side = 1 then hi_ok else lo_ok)
    (hdok : dok = 1 ↔ D0 ≤ C) (hand : cl2 = 1 ↔ cl = 1 ∧ dok = 1) (hck : True → cl2 = 1) :
    LaneClaimR 1 true F0 F1 F2 F3 := by
  intro d x y hd0 hd1 hx0 hx1 _ hy1 hxpi hy
  obtain ⟨-, -, -, -, h09, h1, h11, h32, -, -⟩ := hD
  have h09' : (0.9 : ℝ) ≤ fld F0 0 := h09
  have h1' : fld F0 32 ≤ 1 := h1
  have h11' : (1.1 : ℝ) ≤ fld F1 0 := h11
  have h32' : fld F1 32 ≤ 3.2 := h32
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte]
  show d ≤ fld F3 0
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hcl1, hdok1⟩ := hand.mp (hck trivial)
  rw [hcl, hside] at hcl1
  simp only [zero_ne_one, ↓reduceIte] at hcl1
  have hYO : (Y1 : ℝ) ≤ OL := by exact_mod_cast hlo_ok.mp hcl1
  have hDC : (D0 : ℝ) ≤ C := by exact_mod_cast hdok.mp hdok1
  rw [ix_eq hC, ix_eq hD0] at hDC
  rw [ix_eq hY1] at hYO
  have hc0 : fld F0 0 ≤ fld F3 0 := by nlinarith
  have hcpos : 0 < fld F3 0 := by linarith
  have hdlt : d < π / 2 := by linarith [pi_gt_three]
  have hclt : fld F3 0 < π / 2 := by linarith
  have hdpos : 0 < d := by linarith
  have hxpos : 0 < x := by linarith
  have hxh : 0 < fld F1 32 := by linarith
  have hB := hb trivial (fld F3 0) (fld F1 32) hcpos hclt (enc_pt hC) (enc_pt hX1) hxh
    (by linarith [pi_gt_three])
  have hO := (ho _ _ hB hB).1
  have hmono : rho (fld F3 0) x < rho d x := rho_strictMonoOn_d x ⟨hxpos, hxpi⟩ ⟨hcpos, hclt⟩ ⟨hdpos, hdlt⟩ hlt
  rw [rho_eq_two_bangle ⟨hcpos, hclt⟩ ⟨hxpos, hxpi⟩] at hmono
  have hanti := bangle_anti (fld F3 0) x (fld F1 32) hcpos hclt hxpos hx1 (by linarith [pi_gt_three])
  have : fld F2 32 < y := by
    rw [hy]
    have : 2 ^ 28 * fld F2 32 ≤ 2 ^ 28 * (2 * bangle (fld F3 0) (fld F1 32)) := by linarith
    linarith
  linarith

end Tammes15.D3Trig
