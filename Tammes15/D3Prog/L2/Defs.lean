import Tammes15.D3Ck2.Spec.Scalar
import Tammes15.Trigrows.Defs

namespace D3Prog.L2

open Real Tammes15 D3Ck2Spec

def scI (z : ℤ) : ℕ := if z < 0 then PI_LO + 1 else z.toNat

def sinI (z : ℤ) : ℤ := (sc28pS (scI z)).1

def cosI (z : ℤ) : ℤ := (sc28pS (scI z)).2

def Enc (lo hi : ℤ) (r : ℝ) : Prop := (lo : ℝ) ≤ 2 ^ 28 * r ∧ 2 ^ 28 * r ≤ hi

def AF : Bool → ℤ → ℤ → ℝ → Prop
  | false, lo, hi, θ => Enc lo hi θ
  | true, lo, hi, θ => 0 ≤ lo ∧ 0 ≤ θ ∧ θ ≤ π ∧ Enc lo hi (sin (θ / 2))

noncomputable def fld (F s : ℕ) : ℝ := ((F / 2 ^ s % 2 ^ 32 : ℕ) : ℝ) / 2 ^ 24

noncomputable def pentOut (k : Fin 2) (d x y : ℝ) : ℝ :=
  if k = 0 then bangle d x + gam d (ebase d x) (ebase d y) + bangle d y
  else bangle d x + gam (ebase d y) (ebase d x) d

def FanOK (d x y : ℝ) : Prop :=
  eta d (ebase d x) (ebase d y) ∈ Set.Icc (-1 : ℝ) 1 ∧ eta (ebase d y) (ebase d x) d ∈ Set.Icc (-1 : ℝ) 1 ∧
    eta (ebase d x) (ebase d y) d ∈ Set.Icc (-1 : ℝ) 1

def Claim (hi : Bool) (c v : ℝ) : Prop := if hi then v ≤ c else c ≤ v

def LaneClaim (k : Fin 2) (hi : Bool) (F0 F1 F2 F3 : ℕ) : Prop :=
  ∀ d x y : ℝ, fld F0 0 ≤ d → d ≤ fld F0 32 → fld F1 0 ≤ x → x ≤ fld F1 32 → fld F2 0 ≤ y → y ≤ fld F2 32 →
    x < π → y < π → FanOK d x y → Claim hi (fld F3 0) (pentOut k d x y)

def InDom (F0 F1 F2 F3 : ℕ) : Prop :=
  F0 < 2 ^ 64 ∧ F1 < 2 ^ 64 ∧ F2 < 2 ^ 64 ∧ F3 < 2 ^ 32 ∧
    0.9 ≤ fld F0 0 ∧ fld F0 32 ≤ 1 ∧ 1.1 ≤ fld F1 0 ∧ fld F1 32 ≤ 3.2 ∧ 1.1 ≤ fld F2 0 ∧ fld F2 32 ≤ 3.2

end D3Prog.L2
