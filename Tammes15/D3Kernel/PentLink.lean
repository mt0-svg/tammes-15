import Tammes15.Hyps.Case

open Real

namespace Tammes15.D3Kernel

open Tammes15

def lane (A l : ℕ) : ℕ := A / 2 ^ (64 * l) % 2 ^ 64

def oN (n : ℕ) : ℕ :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft n 6)) 1) 18446744073709551615

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

theorem claim_of_eq {hi : Bool} {c v w : ℝ} (h : Claim hi c v) (hw : w = v) : Claim hi c w := hw ▸ h

theorem laneClaim_pent0 {d u₀ u₁ u₂ u₃ u₄ : ℝ} (hP : PentRel d u₀ u₁ u₂ u₃ u₄) (h1 : u₁ < π) (h4 : u₄ < π)
    {hi : Bool} {F0 F1 F2 F3 : ℕ} (hc : LaneClaim 0 hi F0 F1 F2 F3) (hd : fld F0 0 ≤ d ∧ d ≤ fld F0 32)
    (hx : fld F1 0 ≤ u₁ ∧ u₁ ≤ fld F1 32) (hy : fld F2 0 ≤ u₄ ∧ u₄ ≤ fld F2 32) :
    Claim hi (fld F3 0) u₀ := by
  obtain ⟨he1, he2, he3, hu0, -, -⟩ := hP
  refine claim_of_eq (hc d u₁ u₄ hd.1 hd.2 hx.1 hx.2 hy.1 hy.2 h1 h4 ⟨he1, he2, he3⟩) ?_
  simp [pentOut, hu0]

theorem laneClaim_pent2 {d u₀ u₁ u₂ u₃ u₄ : ℝ} (hP : PentRel d u₀ u₁ u₂ u₃ u₄) (h1 : u₁ < π) (h4 : u₄ < π)
    {hi : Bool} {F0 F1 F2 F3 : ℕ} (hc : LaneClaim 1 hi F0 F1 F2 F3) (hd : fld F0 0 ≤ d ∧ d ≤ fld F0 32)
    (hx : fld F1 0 ≤ u₁ ∧ u₁ ≤ fld F1 32) (hy : fld F2 0 ≤ u₄ ∧ u₄ ≤ fld F2 32) :
    Claim hi (fld F3 0) u₂ := by
  obtain ⟨he1, he2, he3, -, hu2, -⟩ := hP
  refine claim_of_eq (hc d u₁ u₄ hd.1 hd.2 hx.1 hx.2 hy.1 hy.2 h1 h4 ⟨he1, he2, he3⟩) ?_
  simp [pentOut, hu2]

theorem laneClaim_pent3 {d u₀ u₁ u₂ u₃ u₄ : ℝ} (hP : PentRel d u₀ u₁ u₂ u₃ u₄) (h1 : u₁ < π) (h4 : u₄ < π)
    {hi : Bool} {F0 F1 F2 F3 : ℕ} (hc : LaneClaim 1 hi F0 F1 F2 F3) (hd : fld F0 0 ≤ d ∧ d ≤ fld F0 32)
    (hx : fld F1 0 ≤ u₄ ∧ u₄ ≤ fld F1 32) (hy : fld F2 0 ≤ u₁ ∧ u₁ ≤ fld F2 32) :
    Claim hi (fld F3 0) u₃ := by
  obtain ⟨he1, he2, he3, -, -, hu3⟩ := hP
  have hF : FanOK d u₄ u₁ := by
    refine ⟨?_, he3, he2⟩
    simpa [eta, mul_comm] using he1
  refine claim_of_eq (hc d u₄ u₁ hd.1 hd.2 hx.1 hx.2 hy.1 hy.2 h4 h1 hF) ?_
  simp [pentOut, hu3]

theorem laneClaim_relSys {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k} (hA : RelSys P H A)
    {e : P.G.Dart} (he : fsize P e = 5) {hi : Bool} {F0 F1 F2 F3 : ℕ} (hd : fld F0 0 ≤ A.d ∧ A.d ≤ fld F0 32) :
    ((fld F1 0 ≤ A.fc e 1 ∧ A.fc e 1 ≤ fld F1 32) → (fld F2 0 ≤ A.fc e 4 ∧ A.fc e 4 ≤ fld F2 32) →
        (LaneClaim 0 hi F0 F1 F2 F3 → Claim hi (fld F3 0) (A.fc e 0)) ∧
          (LaneClaim 1 hi F0 F1 F2 F3 → Claim hi (fld F3 0) (A.fc e 2))) ∧
      ((fld F1 0 ≤ A.fc e 4 ∧ A.fc e 4 ≤ fld F1 32) → (fld F2 0 ≤ A.fc e 1 ∧ A.fc e 1 ≤ fld F2 32) →
        LaneClaim 1 hi F0 F1 F2 F3 → Claim hi (fld F3 0) (A.fc e 3)) := by
  have hP := hA.pent e he
  have h1 : A.fc e 1 < π := (hA.corner_mem _).2
  have h4 : A.fc e 4 < π := (hA.corner_mem _).2
  exact ⟨fun hx hy => ⟨fun hc => laneClaim_pent0 hP h1 h4 hc hd hx hy,
    fun hc => laneClaim_pent2 hP h1 h4 hc hd hx hy⟩, fun hx hy hc => laneClaim_pent3 hP h1 h4 hc hd hx hy⟩

end Tammes15.D3Kernel
