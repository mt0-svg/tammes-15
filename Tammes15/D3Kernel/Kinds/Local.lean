import Tammes15.D3Kernel.Kinds.LeafEnc
import Tammes15.D3Kernel.Kinds.TieZ
import Tammes15.D3Kernel.Kinds.LocalFarm

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3lp.TrigNat Tammes15.D3Kernel Tammes15.PaperSteps Real
open scoped Classical RealInnerProductSpace

def tcF (lh : ℕ) : Fin 8 := ⟨lhB lh 41 % 8, Nat.mod_lt _ (by norm_num)⟩

def tCon (lh : ℕ) : Fin 15 × Fin 15 := (tieContacts (tcF lh)).getD (lhB lh 42) (0, 0)

def tAB (lh : ℕ) : Fin 15 × Fin 15 := if lhB lh 43 = 0 then tCon lh else (tCon lh).swap

def tMir (lh : ℕ) : Bool := lhB lh 44 != 0

def tJ (lh p : ℕ) : Fin 15 := ⟨lhB lh (45 + p) % 15, Nat.mod_lt _ (by norm_num)⟩

def mZ (lh : ℕ) (i : Fin 15) (l : Fin 3) : ℤ := tmZ (tcF lh) i l

def uZ (lh : ℕ) (l : Fin 3) : ℤ :=
  mZ lh (tAB lh).2 l * 10 ^ 84 -
    (mZ lh (tAB lh).1 0 * mZ lh (tAB lh).2 0 + mZ lh (tAB lh).1 1 * mZ lh (tAB lh).2 1 +
      mZ lh (tAB lh).1 2 * mZ lh (tAB lh).2 2) * mZ lh (tAB lh).1 l

def uSq (lh : ℕ) : ℤ := uZ lh 0 * uZ lh 0 + uZ lh 1 * uZ lh 1 + uZ lh 2 * uZ lh 2

def aZ (lh : ℕ) (q : Fin 15) : ℤ := mZ lh q 0 * uZ lh 0 + mZ lh q 1 * uZ lh 1 + mZ lh q 2 * uZ lh 2

def bZ (lh : ℕ) (q : Fin 15) : ℤ :=
  mZ lh q 0 * (mZ lh (tAB lh).1 1 * uZ lh 2 - mZ lh (tAB lh).1 2 * uZ lh 1) +
    mZ lh q 1 * (mZ lh (tAB lh).1 2 * uZ lh 0 - mZ lh (tAB lh).1 0 * uZ lh 2) +
    mZ lh q 2 * (mZ lh (tAB lh).1 0 * uZ lh 1 - mZ lh (tAB lh).1 1 * uZ lh 0)

def cZ (lh : ℕ) (q : Fin 15) : ℤ :=
  mZ lh q 0 * mZ lh (tAB lh).1 0 + mZ lh q 1 * mZ lh (tAB lh).1 1 + mZ lh q 2 * mZ lh (tAB lh).1 2

def sgnZ (lh : ℕ) : ℤ := if tMir lh then -1 else 1

def mM (lh : ℕ) (q : Fin 15) : Fin 3 → ℤ :=
  ![aZ lh q * lhW lh 152 * 10 ^ 42, sgnZ lh * (bZ lh q * lhW lh 152), cZ lh q * 10 ^ 126 * 2 ^ 62]

def dM : ℤ := 10 ^ 210 * 2 ^ 62

def tN (g box lh p : ℕ) (q : Fin 15) : ℤ :=
  104 * 10 ^ 205 * 2 ^ 64 - ptR g box (hvOf lh) lh (lhB lh 63) p * 10 ^ 210 -
    4 * ((lhW lh 153 : ℤ) - lhW lh 152) * (|aZ lh q| * 10 ^ 42 + |bZ lh q|) - 12000 * (lhW lh 153 : ℤ) * 10 ^ 172

def dT : ℤ := 10 ^ 210 * 2 ^ 64

def f15 (i : ℕ) : Fin 15 := ⟨i % 15, Nat.mod_lt _ (by norm_num)⟩

def localTest (g box lh : ℕ) : Bool :=
  decide (lhB lh 63 + Ctx.k g = 15) && decide (lhB lh 42 < (tieContacts (tcF lh)).length) &&
    allBelow (fun p => allBelow (fun p' => p == p' || !(lhB lh (45 + p) % 15 == lhB lh (45 + p') % 15)) 15) 15 &&
    allBelow (fun i => decide (mZ lh (f15 i) 0 * mZ lh (f15 i) 0 + mZ lh (f15 i) 1 * mZ lh (f15 i) 1 +
      mZ lh (f15 i) 2 * mZ lh (f15 i) 2 ≤ 4 * 10 ^ 84)) 15 &&
    decide ((lhW lh 152 : ℤ) * lhW lh 152 * uSq lh ≤ 2 ^ 124 * 10 ^ 252) &&
    decide (2 ^ 124 * 10 ^ 252 ≤ (lhW lh 153 : ℤ) * lhW lh 153 * uSq lh) && decide (0 < lhW lh 153) &&
    decide (120 * lhW lh 153 ≤ 2 ^ 62 * 10 ^ 38) &&
    allBelow (fun p => decide (0 ≤ tN g box lh p (tJ lh p)) &&
      decide (sq3 (ptM g lh (lhB lh 63) p)
          ⟨0, 0, mM lh (tJ lh p) 0, 0, 0, mM lh (tJ lh p) 1, 0, 0, mM lh (tJ lh p) 2⟩ (ptQ g lh (lhB lh 63) p) dM *
          (dT * dT) ≤ (tN g box lh p (tJ lh p) * ptQ g lh (lhB lh 63) p * dM) *
            (tN g box lh p (tJ lh p) * ptQ g lh (lhB lh 63) p * dM))) 15

def localOK (g box it : ℕ) : Bool := encOK g box (it / 2 ^ 128) && localTest g box (it / 2 ^ 128)

theorem lc_sub3 (a0 a1 a2 b0 b1 b2 : ℝ) :
    (!₂[a0, a1, a2] : EuclideanSpace ℝ (Fin 3)) - !₂[b0, b1, b2] = !₂[a0 - b0, a1 - b1, a2 - b2] := by
  ext i
  fin_cases i <;> simp

theorem lc_smul3 (k a0 a1 a2 : ℝ) :
    k • (!₂[a0, a1, a2] : EuclideanSpace ℝ (Fin 3)) = !₂[k * a0, k * a1, k * a2] := by
  ext i
  fin_cases i <;> simp

theorem lc_ofLp3 (a0 a1 a2 : ℝ) :
    (!₂[a0, a1, a2] : EuclideanSpace ℝ (Fin 3)).ofLp 0 = a0 ∧ (!₂[a0, a1, a2] : EuclideanSpace ℝ (Fin 3)).ofLp 1 = a1 ∧
      (!₂[a0, a1, a2] : EuclideanSpace ℝ (Fin 3)).ofLp 2 = a2 := by
  simp

theorem rLocal_eq : rLocal = 104 / 10 ^ 5 := by
  unfold rLocal
  norm_num

section LocalSound

variable {g : ℕ}

def ptIdx {s : Sol g} : Pts s.P (Ctx.k g) → ℕ
  | .inl v => v
  | .inr m => s.P.n + m

theorem ptIdx_lt (s : Sol g) (x : Pts s.P (Ctx.k g)) : ptIdx x < s.P.n + Ctx.k g := by
  cases x with
  | inl v => exact lt_of_lt_of_le v.isLt (Nat.le_add_right _ _)
  | inr m => show s.P.n + (m : ℕ) < _; have := m.isLt; omega

theorem ptOf_ptIdx (s : Sol g) (hn : 0 < s.P.n) (x : Pts s.P (Ctx.k g)) : ptOf s hn s.P.n (ptIdx x) = x := by
  cases x with
  | inl v =>
    show ptOf s hn s.P.n v = _
    unfold ptOf
    rw [ite_eq_left v.isLt]
    congr 1
    exact Fin.ext (vertOf_val s hn v.isLt)
  | inr m =>
    show ptOf s hn s.P.n (s.P.n + m) = _
    unfold ptOf
    have h1 : ¬ s.P.n + (m : ℕ) < s.P.n := by omega
    have h2 : s.P.n + (m : ℕ) - s.P.n < Ctx.k g := by have := m.isLt; omega
    rw [ite_eq_right h1, dite_eq_left h2]
    congr 1
    exact Fin.ext (by simp)

noncomputable def mV (c : Fin 8) (i : Fin 15) : EuclideanSpace ℝ (Fin 3) := !₂[tieMid c i 0, tieMid c i 1, tieMid c i 2]

theorem mV_eq (lh : ℕ) (i : Fin 15) :
    mV (tcF lh) i = !₂[(mZ lh i 0 : ℝ) / 10 ^ 42, (mZ lh i 1 : ℝ) / 10 ^ 42, (mZ lh i 2 : ℝ) / 10 ^ 42] := by
  unfold mV
  rw [tieMid_eq, tieMid_eq, tieMid_eq]
  rfl

theorem u0_eq (lh : ℕ) :
    mV (tcF lh) (tAB lh).2 - inner ℝ (mV (tcF lh) (tAB lh).1) (mV (tcF lh) (tAB lh).2) • mV (tcF lh) (tAB lh).1 =
      !₂[(uZ lh 0 : ℝ) / 10 ^ 126, (uZ lh 1 : ℝ) / 10 ^ 126, (uZ lh 2 : ℝ) / 10 ^ 126] := by
  rw [mV_eq, mV_eq, lc_inner3, lc_smul3, lc_sub3]
  unfold uZ
  push_cast
  congr 1
  ring_nf

theorem abc_eq (lh : ℕ) (q : Fin 15) :
    inner ℝ (mV (tcF lh) q) (!₂[(uZ lh 0 : ℝ) / 10 ^ 126, (uZ lh 1 : ℝ) / 10 ^ 126, (uZ lh 2 : ℝ) / 10 ^ 126]) =
        (aZ lh q : ℝ) / 10 ^ 168 ∧
      inner ℝ (mV (tcF lh) q) (cross (mV (tcF lh) (tAB lh).1)
        !₂[(uZ lh 0 : ℝ) / 10 ^ 126, (uZ lh 1 : ℝ) / 10 ^ 126, (uZ lh 2 : ℝ) / 10 ^ 126]) = (bZ lh q : ℝ) / 10 ^ 210 ∧
      inner ℝ (mV (tcF lh) q) (mV (tcF lh) (tAB lh).1) = (cZ lh q : ℝ) / 10 ^ 84 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mV_eq, lc_inner3]
    unfold aZ
    push_cast
    ring
  · rw [mV_eq, mV_eq, lc_cross3, lc_inner3]
    unfold bZ
    push_cast
    ring
  · rw [mV_eq, mV_eq, lc_inner3]
    unfold cZ
    push_cast
    ring

theorem mV_norm (lh : ℕ) (i : Fin 15)
    (h : mZ lh i 0 * mZ lh i 0 + mZ lh i 1 * mZ lh i 1 + mZ lh i 2 * mZ lh i 2 ≤ 4 * 10 ^ 84) :
    ‖mV (tcF lh) i‖ ≤ 2 := by
  rw [mV_eq]
  apply lc_norm_le_two
  have h' : ((mZ lh i 0 * mZ lh i 0 + mZ lh i 1 * mZ lh i 1 + mZ lh i 2 * mZ lh i 2 : ℤ) : ℝ) ≤ 4 * 10 ^ 84 := by
    exact_mod_cast h
  push_cast at h'
  have e : ((mZ lh i 0 : ℝ) / 10 ^ 42) ^ 2 + ((mZ lh i 1 : ℝ) / 10 ^ 42) ^ 2 + ((mZ lh i 2 : ℝ) / 10 ^ 42) ^ 2 =
      ((mZ lh i 0 : ℝ) * mZ lh i 0 + mZ lh i 1 * mZ lh i 1 + mZ lh i 2 * mZ lh i 2) / 10 ^ 84 := by ring
  rw [e, div_le_iff₀ (by norm_num)]
  linarith

theorem box_near (c : Fin 8) (z : Fin 15 → EuclideanSpace ℝ (Fin 3)) (hz : InTieBoxes c z) (i : Fin 15) :
    ‖z i - mV c i‖ ≤ 3 / 10 ^ 38 := by
  have h := lc_box_norm (z i) (tieMid c i) (fun _ => 1 / 10 ^ 38) (fun l => by rw [← tieRad_eq c i l]; exact hz i l)
  unfold mV
  have e : (1 : ℝ) / 10 ^ 38 + 1 / 10 ^ 38 + 1 / 10 ^ 38 = 3 / 10 ^ 38 := by ring
  rw [← e]
  exact h
theorem ptOf_ptIdx' (s : Sol g) (hn : 0 < s.P.n) {n : ℕ} (hn' : s.P.n = n) (x : Pts s.P (Ctx.k g)) :
    ptOf s hn n (ptIdx x) = x := by
  subst hn'
  exact ptOf_ptIdx s hn x

theorem ptIdx_inj (s : Sol g) : Function.Injective (ptIdx (s := s)) := by
  intro x y h
  cases x with
  | inl v =>
    cases y with
    | inl w => exact congrArg Sum.inl (Fin.ext h)
    | inr m =>
      exfalso
      have h' : (v : ℕ) = s.P.n + m := h
      have := v.isLt
      omega
  | inr m =>
    cases y with
    | inl w =>
      exfalso
      have h' : s.P.n + (m : ℕ) = w := h
      have := w.isLt
      omega
    | inr m' =>
      have h' : s.P.n + (m : ℕ) = s.P.n + m' := h
      exact congrArg Sum.inr (Fin.ext (by omega))

theorem lc_vec3 {a0 a1 a2 b0 b1 b2 : ℝ} (h0 : a0 = b0) (h1 : a1 = b1) (h2 : a2 = b2) :
    (!₂[a0, a1, a2] : EuclideanSpace ℝ (Fin 3)) = !₂[b0, b1, b2] := by
  subst h0 h1 h2
  rfl

theorem lc_budget (R a b L1 L2 : ℝ) :
    (104 * 10 ^ 205 * 2 ^ 64 - R * 10 ^ 210 - 4 * (L2 - L1) * (|a| * 10 ^ 42 + |b|) - 12000 * L2 * 10 ^ 172) /
        (10 ^ 210 * 2 ^ 64) + (L2 / 2 ^ 62 - L1 / 2 ^ 62) * (|a / 10 ^ 168| + |b / 10 ^ 210|) +
        1000 * (3 / 10 ^ 38) / (L2 / 2 ^ 62)⁻¹ + R / 2 ^ 64 = 104 / 10 ^ 5 := by
  rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10 ^ 168),
    abs_of_pos (by norm_num : (0 : ℝ) < 10 ^ 210), div_inv_eq_mul]
  field_simp
  ring

theorem local_mid {lh : ℕ} (q : Fin 15)
    (hl1 : (lhW lh 152 : ℤ) * lhW lh 152 * uSq lh ≤ 2 ^ 124 * 10 ^ 252)
    (hl2 : 2 ^ 124 * 10 ^ 252 ≤ (lhW lh 153 : ℤ) * lhW lh 153 * uSq lh) :
    ((lhW lh 153 : ℝ) / 2 ^ 62)⁻¹ ≤
        ‖mV (tcF lh) (tAB lh).2 - inner ℝ (mV (tcF lh) (tAB lh).1) (mV (tcF lh) (tAB lh).2) • mV (tcF lh) (tAB lh).1‖ ∧
      ‖(!₂[(mM lh q 0 : ℝ) / dM, (mM lh q 1 : ℝ) / dM, (mM lh q 2 : ℝ) / dM] : EuclideanSpace ℝ (Fin 3)) -
          tieNormalize (mV (tcF lh) (tAB lh).1) (mV (tcF lh) (tAB lh).2) (tMir lh) (mV (tcF lh) q)‖ ≤
        ((lhW lh 153 : ℝ) / 2 ^ 62 - (lhW lh 152 : ℝ) / 2 ^ 62) *
          (|(aZ lh q : ℝ) / 10 ^ 168| + |(bZ lh q : ℝ) / 10 ^ 210|) := by
  have hsq : ∀ L : ℝ, L ^ 2 * (((uZ lh 0 : ℝ) / 10 ^ 126) ^ 2 + ((uZ lh 1 : ℝ) / 10 ^ 126) ^ 2 +
      ((uZ lh 2 : ℝ) / 10 ^ 126) ^ 2) = L ^ 2 * (uSq lh : ℝ) / 10 ^ 252 := by
    intro L
    unfold uSq
    push_cast
    ring
  have hl1' : ((lhW lh 152 : ℝ) / 2 ^ 62) ^ 2 * (((uZ lh 0 : ℝ) / 10 ^ 126) ^ 2 + ((uZ lh 1 : ℝ) / 10 ^ 126) ^ 2 +
      ((uZ lh 2 : ℝ) / 10 ^ 126) ^ 2) ≤ 1 := by
    rw [hsq]
    have h' : ((lhW lh 152 : ℤ) : ℝ) * (lhW lh 152 : ℤ) * (uSq lh : ℝ) ≤ 2 ^ 124 * 10 ^ 252 := by exact_mod_cast hl1
    push_cast at h'
    rw [div_le_one (by norm_num), div_pow, div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
    nlinarith
  have hl2' : 1 ≤ ((lhW lh 153 : ℝ) / 2 ^ 62) ^ 2 * (((uZ lh 0 : ℝ) / 10 ^ 126) ^ 2 +
      ((uZ lh 1 : ℝ) / 10 ^ 126) ^ 2 + ((uZ lh 2 : ℝ) / 10 ^ 126) ^ 2) := by
    rw [hsq]
    have h' : (2 : ℝ) ^ 124 * 10 ^ 252 ≤ ((lhW lh 153 : ℤ) : ℝ) * (lhW lh 153 : ℤ) * (uSq lh : ℝ) := by
      exact_mod_cast hl2
    push_cast at h'
    rw [one_le_div (by norm_num), div_pow, div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
    nlinarith
  obtain ⟨hne, ht1, ht2⟩ := lc_inv_norm_mem (l1 := (lhW lh 152 : ℝ) / 2 ^ 62) (l2 := (lhW lh 153 : ℝ) / 2 ^ 62)
    (u := !₂[(uZ lh 0 : ℝ) / 10 ^ 126, (uZ lh 1 : ℝ) / 10 ^ 126,
    (uZ lh 2 : ℝ) / 10 ^ 126]) (div_nonneg (Nat.cast_nonneg _) (by norm_num))
    (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (by simpa using hl1') (by simpa using hl2')
  rw [u0_eq]
  refine ⟨?_, ?_⟩
  · exact inv_le_of_inv_le₀ (norm_pos_iff.mpr hne) ht2
  · rw [lc_tieN_expand, u0_eq, (abc_eq lh q).1, (abc_eq lh q).2.1, (abc_eq lh q).2.2, norm_sub_rev]
    have hs : |(if tMir lh then -1 else 1 : ℝ)| = 1 := by split_ifs <;> simp
    have e : (!₂[(mM lh q 0 : ℝ) / dM, (mM lh q 1 : ℝ) / dM, (mM lh q 2 : ℝ) / dM] : EuclideanSpace ℝ (Fin 3)) =
        !₂[(aZ lh q : ℝ) / 10 ^ 168 * ((lhW lh 152 : ℝ) / 2 ^ 62),
          (if tMir lh then -1 else 1 : ℝ) * ((bZ lh q : ℝ) / 10 ^ 210 * ((lhW lh 152 : ℝ) / 2 ^ 62)),
          (cZ lh q : ℝ) / 10 ^ 84] := by
      apply lc_vec3
      · simp only [mM, dM, Matrix.cons_val_zero]
        push_cast
        field_simp
        ring
      · simp only [mM, dM, sgnZ, Matrix.cons_val_one, Matrix.cons_val_zero]
        split_ifs <;> push_cast <;> field_simp <;> ring
      · simp only [mM, dM, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        push_cast
        field_simp
        ring
    rw [e]
    exact lc_mid_close ht1 ht2 hs

theorem local_point (s : Sol g) (hn : 0 < s.P.n) (hD : 0 < Ctx.D g) {box lh : ℕ} (hn' : s.P.n = lhB lh 63)
    (hr : lhB lh 1 < s.P.n)
    (hpar : ∀ v : Fin s.P.n, v ≠ (glueOf s hn hD lh).root → lhB lh (3 + v) < Ctx.D g)
    {p : ℕ} (hp : p < lhB lh 63 + Ctx.k g) (q : Fin 15) (htN : 0 ≤ tN g box lh p q)
    (hsq : sq3 (ptM g lh (lhB lh 63) p) ⟨0, 0, mM lh q 0, 0, 0, mM lh q 1, 0, 0, mM lh q 2⟩
        (ptQ g lh (lhB lh 63) p) dM * (dT * dT) ≤
      (tN g box lh p q * ptQ g lh (lhB lh 63) p * dM) * (tN g box lh p q * ptQ g lh (lhB lh 63) p * dM)) :
    ‖glueC s.H (glueOf s hn hD lh) (enclF s hn hD box (hvOf lh) lh (lhB lh 63)) (ptOf s hn (lhB lh 63) p) -
          !₂[(mM lh q 0 : ℝ) / dM, (mM lh q 1 : ℝ) / dM, (mM lh q 2 : ℝ) / dM]‖ ≤ (tN g box lh p q : ℝ) / dT ∧
      radC s.H (glueOf s hn hD lh) (enclF s hn hD box (hvOf lh) lh (lhB lh 63)) (ptOf s hn (lhB lh 63) p) =
        (ptR g box (hvOf lh) lh (lhB lh 63) p : ℝ) / 2 ^ 64 := by
  obtain ⟨hg, hrad⟩ := pt_spec s hn hD (box := box) hn' hr hpar hp
  refine ⟨?_, hrad⟩
  rw [hg]
  obtain ⟨c0, c1, c2⟩ := pr_col3 (ptM g lh (lhB lh 63) p) (1 / (ptQ g lh (lhB lh 63) p : ℝ))
  obtain ⟨d0, d1, d2⟩ := lc_ofLp3 ((mM lh q 0 : ℝ) / dM) ((mM lh q 1 : ℝ) / dM) ((mM lh q 2 : ℝ) / dM)
  exact lc_dist_le (ptQ_pos g lh _ _) (by unfold dM; norm_num) htN (by unfold dT; norm_num)
    ⟨by rw [c0]; ring, by rw [c1]; ring, by rw [c2]; ring⟩ ⟨d0, d1, d2⟩ hsq

theorem local_budget {g box lh p : ℕ} (q : Fin 15) :
    (tN g box lh p q : ℝ) / dT + ((lhW lh 153 : ℝ) / 2 ^ 62 - (lhW lh 152 : ℝ) / 2 ^ 62) *
        (|(aZ lh q : ℝ) / 10 ^ 168| + |(bZ lh q : ℝ) / 10 ^ 210|) +
        1000 * (3 / 10 ^ 38) / ((lhW lh 153 : ℝ) / 2 ^ 62)⁻¹ + (ptR g box (hvOf lh) lh (lhB lh 63) p : ℝ) / 2 ^ 64 =
      rLocal := by
  have e1 : (tN g box lh p q : ℝ) = 104 * 10 ^ 205 * 2 ^ 64 - (ptR g box (hvOf lh) lh (lhB lh 63) p : ℝ) * 10 ^ 210 -
      4 * ((lhW lh 153 : ℝ) - lhW lh 152) * (|(aZ lh q : ℝ)| * 10 ^ 42 + |(bZ lh q : ℝ)|) -
      12000 * (lhW lh 153 : ℝ) * 10 ^ 172 := by
    unfold tN
    push_cast
    ring
  have e2 : (dT : ℝ) = 10 ^ 210 * 2 ^ 64 := by
    unfold dT
    push_cast
    ring
  rw [e1, e2, rLocal_eq]
  exact lc_budget _ _ _ _ _

theorem localOK_sound {box it : ℕ} (h : localOK g box it = true) : KillOK g box := by
  simp only [localOK, Bool.and_eq_true] at h
  obtain ⟨henc, hloc⟩ := h
  set lh := it / 2 ^ 128 with hlh
  obtain ⟨hvm, hverts, hglue, -, -, -, -, -, -⟩ := encOK_facts henc
  obtain ⟨hD, hr, -, hpar0⟩ := glueOK_facts hglue
  simp only [localTest, Bool.and_eq_true, decide_eq_true_eq, allBelow_iff] at hloc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hnk, hcl⟩, hinj⟩, hmid⟩, hl1⟩, hl2⟩, hl2pos⟩, hl2small⟩, hpts⟩ := hloc
  apply killOK_of_leafKill procsW_sound hvm
  intro s hs
  have hn' : s.P.n = lhB lh 63 := sol_n s hverts
  have hn : 0 < s.P.n := by omega
  have hD' : 0 < Ctx.D g := hD
  have hr' : lhB lh 1 < s.P.n := by omega
  have hpar := par_lt s hn hD' hn' hr' hpar0
  refine ⟨glueOf s hn hD' lh, glueOf_valid s hn' hn hD' hglue, enclF s hn hD' box (hvOf lh) lh (lhB lh 63),
    encl_covers henc s hs hn hD', Or.inr ?_⟩

  have hjinj : Function.Injective (fun x : Pts s.P (Ctx.k g) => tJ lh (ptIdx x)) := by
    intro x y hxy
    apply ptIdx_inj s
    have hx := ptIdx_lt s x
    have hy := ptIdx_lt s y
    have hv : lhB lh (45 + ptIdx x) % 15 = lhB lh (45 + ptIdx y) % 15 := congrArg Fin.val hxy
    have := hinj (ptIdx x) (by omega) (ptIdx y) (by omega)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at this
    rcases this with h1 | h1
    · exact h1
    · exact absurd hv h1
  have hbij : Function.Bijective (fun x : Pts s.P (Ctx.k g) => tJ lh (ptIdx x)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hjinj, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
  refine ⟨tcF lh, tCon lh, ?_, tAB lh, ?_, tMir lh, Equiv.ofBijective _ hbij, ?_⟩
  · unfold tCon
    rw [List.getD_eq_getElem _ _ hcl]
    exact List.getElem_mem hcl
  · unfold tAB
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  intro z hz v
  rw [Equiv.ofBijective_apply]
  set p := ptIdx v with hp_def
  have hp : p < lhB lh 63 + Ctx.k g := by have := ptIdx_lt s v; omega
  have hp15 : p < 15 := by omega
  obtain ⟨htN, hsq⟩ := hpts p hp15
  obtain ⟨hYM, hrad⟩ := local_point s hn hD' hn' hr' hpar hp (tJ lh p) htN hsq
  have hvp : ptOf s hn (lhB lh 63) p = v := ptOf_ptIdx' s hn hn' v
  rw [hvp] at hYM hrad

  have hnm : ∀ i : Fin 15, ‖mV (tcF lh) i‖ ≤ 2 := by
    intro i
    apply mV_norm
    have := hmid i i.isLt
    have hf : f15 (i : ℕ) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [hf] at this
    exact this
  obtain ⟨hμu, hMN⟩ := local_mid (tJ lh p) hl1 hl2
  have hl2r : (0 : ℝ) < (lhW lh 153 : ℝ) / 2 ^ 62 := by
    have : (0 : ℝ) < (lhW lh 153 : ℝ) := by exact_mod_cast hl2pos
    exact div_pos this (by norm_num)
  have hsmall : 40 * (3 / 10 ^ 38 : ℝ) ≤ ((lhW lh 153 : ℝ) / 2 ^ 62)⁻¹ := by
    rw [inv_div, le_div_iff₀ (by exact_mod_cast hl2pos)]
    have : ((120 * lhW lh 153 : ℕ) : ℝ) ≤ ((2 ^ 62 * 10 ^ 38 : ℕ) : ℝ) := by exact_mod_cast hl2small
    push_cast at this
    linarith
  have hpert := lc_tie_pert (za := z (tAB lh).1) (zb := z (tAB lh).2) (zq := z (tJ lh p))
    (a := mV (tcF lh) (tAB lh).1) (b := mV (tcF lh) (tAB lh).2) (q := mV (tcF lh) (tJ lh p))
    (ρ := 3 / 10 ^ 38) (μ := ((lhW lh 153 : ℝ) / 2 ^ 62)⁻¹) (tMir lh)
    (box_near _ z hz _) (box_near _ z hz _) (box_near _ z hz _) (by norm_num) (hnm _) (hnm _) (hnm _)
    (inv_pos.mpr hl2r) hsmall hμu
  rw [norm_sub_rev] at hpert
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (glueC s.H (glueOf s hn hD' lh) (enclF s hn hD' box (hvOf lh) lh (lhB lh 63)) v)
    (!₂[(mM lh (tJ lh p) 0 : ℝ) / dM, (mM lh (tJ lh p) 1 : ℝ) / dM, (mM lh (tJ lh p) 2 : ℝ) / dM])
    (tieNormalize (z (tAB lh).1) (z (tAB lh).2) (tMir lh) (z (tJ lh p)))
  have htri2 := norm_sub_le_norm_sub_add_norm_sub
    (!₂[(mM lh (tJ lh p) 0 : ℝ) / dM, (mM lh (tJ lh p) 1 : ℝ) / dM, (mM lh (tJ lh p) 2 : ℝ) / dM] :
      EuclideanSpace ℝ (Fin 3))
    (tieNormalize (mV (tcF lh) (tAB lh).1) (mV (tcF lh) (tAB lh).2) (tMir lh) (mV (tcF lh) (tJ lh p)))
    (tieNormalize (z (tAB lh).1) (z (tAB lh).2) (tMir lh) (z (tJ lh p)))
  have hb := local_budget (g := g) (box := box) (lh := lh) (p := p) (tJ lh p)
  rw [hrad]
  linarith

end LocalSound

def localChecker : Checker := killChecker localOK

theorem localChecker_sound : localChecker.Sound (kindIs 10) :=
  killChecker_sound localOK (fun _ _ _ h => localOK_sound h) _

end Tammes15.D3Kernel.Kinds
