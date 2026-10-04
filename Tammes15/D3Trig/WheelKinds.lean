import Tammes15.D3Trig.WheelLink
import Tammes15.D3Trig.HexKinds

open Real

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel
open D3Prog.L2 (Enc AF)

theorem encPt {F s : ℕ} {V : ℤ} (hV : V = ((F / 2 ^ s % 2 ^ 32 * 16 : ℕ) : ℤ)) : Enc V V (fld F s) := by
  have h := divH hV
  have h2 : (2 : ℝ) ^ 28 * fld F s = V := by rw [← h]; field_simp
  exact ⟨h2.symm.le, h2.le⟩

theorem TWL (F0 F1 F2 F3 : ℕ) (_hD : InDomW F0 F1 F2 F3) (D0 D1 R0 R1 P Q T : ℤ) (G1L G1H G2L G2H SL SH : ℤ)
    (lt : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hR0 : R0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hR1 : R1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hP : P = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hQ : Q = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hT : T = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hg1 : True → ∀ θg θe θf : ℝ, AF false P P θg → AF false R0 R1 θe → AF false D0 D1 θf →
      Enc G1L G1H (gam θg θe θf))
    (hg2 : True → ∀ θg θe θf : ℝ, AF false Q Q θg → AF false R0 R1 θe → AF false D0 D1 θf →
      Enc G2L G2H (gam θg θe θf))
    (hs : ∀ r s : ℝ, Enc G1L G1H r → Enc G2L G2H s → Enc SL SH (r + s))
    (hlt : lt = 1 ↔ T < SL) (hck : True → lt = 1) :
    LaneClaimW false F0 F1 F2 F3 := by
  intro d r hd1 hd2 hr1 hr2
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hdE : Enc D0 D1 d := encH hD0 hD1 hd1 hd2
  have hrE : Enc R0 R1 r := encH hR0 hR1 hr1 hr2
  have h1 := hg1 trivial _ r d (encPt hP) hrE hdE
  have h2 := hg2 trivial _ r d (encPt hQ) hrE hdE
  have hS := hs _ _ h1 h2
  have hTS : (T : ℝ) < SL := by exact_mod_cast hlt.mp (hck trivial)
  have hT' := divH hT
  unfold wheelOut
  rw [← hT']
  have := hS.1
  rw [div_lt_iff₀ (by positivity)]
  linarith

theorem TWH (F0 F1 F2 F3 : ℕ) (_hD : InDomW F0 F1 F2 F3) (D0 D1 R0 R1 P Q T : ℤ) (G1L G1H G2L G2H SL SH : ℤ)
    (lt : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hR0 : R0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hR1 : R1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hP : P = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hQ : Q = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hT : T = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hg1 : True → ∀ θg θe θf : ℝ, AF false P P θg → AF false R0 R1 θe → AF false D0 D1 θf →
      Enc G1L G1H (gam θg θe θf))
    (hg2 : True → ∀ θg θe θf : ℝ, AF false Q Q θg → AF false R0 R1 θe → AF false D0 D1 θf →
      Enc G2L G2H (gam θg θe θf))
    (hs : ∀ r s : ℝ, Enc G1L G1H r → Enc G2L G2H s → Enc SL SH (r + s))
    (hlt : lt = 1 ↔ SH < T) (hck : True → lt = 1) :
    LaneClaimW true F0 F1 F2 F3 := by
  intro d r hd1 hd2 hr1 hr2
  simp only [↓reduceIte]
  have hdE : Enc D0 D1 d := encH hD0 hD1 hd1 hd2
  have hrE : Enc R0 R1 r := encH hR0 hR1 hr1 hr2
  have h1 := hg1 trivial _ r d (encPt hP) hrE hdE
  have h2 := hg2 trivial _ r d (encPt hQ) hrE hdE
  have hS := hs _ _ h1 h2
  have hTS : (SH : ℝ) < T := by exact_mod_cast hlt.mp (hck trivial)
  have hT' := divH hT
  unfold wheelOut
  rw [← hT']
  have := hS.2
  rw [lt_div_iff₀ (by positivity)]
  linarith

theorem TWSH (F0 F1 F2 F3 : ℕ) (_hD : InDomWS F0 F1 F2 F3) (D0 D1 R0 R1 S0 S1 B : ℤ) (GLo GHi : ℤ) (lt : ℕ)
    (hD0 : D0 = ((F0 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hD1 : D1 = ((F0 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hR0 : R0 = ((F1 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hR1 : R1 = ((F1 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hS0 : S0 = ((F2 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ)) (hS1 : S1 = ((F2 / 2 ^ 32 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hB : B = ((F3 / 2 ^ 0 % 2 ^ 32 * 16 : ℕ) : ℤ))
    (hg : True → ∀ θg θe θf : ℝ, AF false D0 D1 θg → AF false R0 R1 θe → AF false S0 S1 θf →
      Enc GLo GHi (gam θg θe θf))
    (hlt : lt = 1 ↔ GHi < B) (hck : True → lt = 1) :
    LaneClaimWS F0 F1 F2 F3 := by
  intro d r r' hd1 hd2 hr1 hr2 hs1 hs2
  have h := hg trivial d r r' (encH hD0 hD1 hd1 hd2) (encH hR0 hR1 hr1 hr2) (encH hS0 hS1 hs1 hs2)
  have hGB : (GHi : ℝ) < B := by exact_mod_cast hlt.mp (hck trivial)
  rw [← divH hB, lt_div_iff₀ (by positivity)]
  linarith [h.2]

end Tammes15.D3Trig
