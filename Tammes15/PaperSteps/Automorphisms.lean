/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
import Tammes15.Nonunique.Corollary
import Tammes15.PaperSteps.Optima

/-!
# The automorphisms of the contact graphs and the orthogonal maps preserving C1 and C3

`aut_contactGraph_C1`: the only automorphism of the contact graph of `C1` is the identity;
`aut_contactGraph_C3`: those of the contact graph of `C3` are the permutations `p ↦ ζ^i p`,
`i = 0, 1, 2`, with `ζ = rhoL`, `ζ (x, y, z) = (z, x, y)`. `orthogonal_C1`, `orthogonal_C3`: the
orthogonal maps that map `C1` onto `C1` are the identity, those that map `C3` onto `C3` are `1`, `ζ`
and `ζ²`; `orthogonal_det`: all of them are rotations.

The graphs are told apart by colour refinement. A colouring `c'` refines `c` (`Refines`) when two
vertices of the same colour under `c` whose neighbours carry the same colours under `c`, counted
with multiplicity, have the same colour under `c'`; a permutation that preserves the adjacency and
`c` then preserves `c'` (`Refines.perm`). The colourings of the rounds are listed below and each
step is checked by `decide`. For `C1` the fifth round gives fifteen colours, so an automorphism
fixes every vertex. For `C3` the second round puts `0` in the class `{0, 1, 2}`, so an automorphism
composed with a power of `zeta3`, the action of `ζ` on the labels, fixes `0`; refinement from the
colouring that singles out `0` gives fifteen colours in three rounds, so that composite is the
identity.

An orthogonal map that maps one of the two configurations onto itself permutes its points and keeps
their inner products, so it induces an automorphism of the contact graph and agrees with `ζ^i` on
the points. The points `p_V, ζ p_V, ζ² p_V` (labels `0, 1, 2` of both configurations) span `ℝ³`
(`eq_zero_of_inner_pV`, from the enclosures of their coordinates), so the map is `ζ^i`.
-/

open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Attained

/-! ## Colour refinement -/

section Refine

variable {n : ℕ}

/-- The colours under `c` of the neighbours of `v`, counted with multiplicity in base 16. -/
def nbCount (adj : Fin n → Fin n → Bool) (c : Fin n → ℕ) (v : Fin n) : ℕ :=
  ∑ w, if adj v w then 16 ^ c w else 0

/-- `c'` is a function of the colour under `c` and of the neighbour count `nbCount adj c`. -/
def Refines (adj : Fin n → Fin n → Bool) (c c' : Fin n → ℕ) : Prop :=
  ∀ v w, c v = c w → nbCount adj c v = nbCount adj c w → c' v = c' w

instance (adj : Fin n → Fin n → Bool) (c c' : Fin n → ℕ) : Decidable (Refines adj c c') := by
  unfold Refines; infer_instance

theorem nbCount_perm {adj : Fin n → Fin n → Bool} {c : Fin n → ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ a b, adj (σ a) (σ b) = adj a b) (hc : ∀ v, c (σ v) = c v) (v : Fin n) :
    nbCount adj c (σ v) = nbCount adj c v := by
  unfold nbCount
  rw [← Equiv.sum_comp σ]
  simp only [hσ, hc]

/-- A permutation that preserves the adjacency and `c` preserves every refinement of `c`. -/
theorem Refines.perm {adj : Fin n → Fin n → Bool} {c c' : Fin n → ℕ} (h : Refines adj c c')
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ a b, adj (σ a) (σ b) = adj a b) (hc : ∀ v, c (σ v) = c v) :
    ∀ v, c' (σ v) = c' v :=
  fun v => h _ _ (hc v) (nbCount_perm hσ hc v)

end Refine

/-! ## The two graphs as bitmasks -/

/-- The adjacency of a graph on `Fin 15` given by one bitmask per vertex. -/
def adjOf (m : Fin 15 → ℕ) (v w : Fin 15) : Bool := (m v).testBit w

/-- The neighbours of each vertex of `listGraph S1`, as a bitmask. -/
def maskC1 : Fin 15 → ℕ :=
  ![110, 157, 51, 643, 2310, 1093, 545, 2058, 17424, 12360, 24864, 20624, 27136, 22016, 15616]

/-- The neighbours of each vertex of `listGraph S3`, as a bitmask. -/
def maskC3 : Fin 15 → ℕ :=
  ![110, 157, 307, 643, 2310, 1093, 545, 2058, 1044, 12360, 24864, 20624, 27136, 22016, 15360]

theorem listGraph_S1_adj :
    ∀ a b, (Nonunique.listGraph Nonunique.S1).Adj a b ↔ adjOf maskC1 a b = true := by
  decide

theorem listGraph_S3_adj :
    ∀ a b, (Nonunique.listGraph Nonunique.S3).Adj a b ↔ adjOf maskC3 a b = true := by
  decide

theorem adjOf_perm {G : SimpleGraph (Fin 15)} {m : Fin 15 → ℕ}
    (hG : ∀ a b, G.Adj a b ↔ adjOf m a b = true) {σ : Equiv.Perm (Fin 15)}
    (hσ : ∀ a b, G.Adj (σ a) (σ b) ↔ G.Adj a b) : ∀ a b, adjOf m (σ a) (σ b) = adjOf m a b := by
  intro a b
  apply Bool.eq_iff_iff.mpr
  rw [← hG, ← hG]
  exact hσ a b

/-! ## C1: refinement to fifteen colours -/

/-- The rounds of colour refinement on the contact graph of `C1`, from the constant colouring. -/
def colC1 : Fin 6 → Fin 15 → ℕ :=
  ![fun _ => 0,
    ![2, 2, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 2],
    ![7, 7, 5, 4, 2, 2, 0, 0, 0, 1, 2, 2, 3, 3, 6],
    ![10, 10, 8, 7, 5, 5, 1, 2, 0, 3, 4, 4, 6, 6, 9],
    ![12, 13, 10, 9, 6, 7, 1, 2, 0, 3, 4, 5, 8, 8, 11],
    ![13, 14, 11, 10, 6, 7, 1, 2, 0, 3, 4, 5, 9, 8, 12]]

theorem colC1_refines : ∀ k : Fin 5, Refines (adjOf maskC1) (colC1 k.castSucc) (colC1 k.succ) := by
  decide

theorem colC1_injective : Function.Injective (colC1 5) := by
  decide

/-- An automorphism of `listGraph S1` is the identity. -/
theorem perm_S1_eq_one (σ : Equiv.Perm (Fin 15))
    (hσ : ∀ a b, (Nonunique.listGraph Nonunique.S1).Adj (σ a) (σ b) ↔
      (Nonunique.listGraph Nonunique.S1).Adj a b) : σ = 1 := by
  have hadj := adjOf_perm listGraph_S1_adj hσ
  have hcol : ∀ k : Fin 6, ∀ v, colC1 k (σ v) = colC1 k v := by
    intro k
    induction k using Fin.induction with
    | zero => intro v; rfl
    | succ k ih => exact (colC1_refines k).perm hadj ih
  ext v
  exact congrArg Fin.val (colC1_injective (hcol 5 v))

/-! ## C3: the permutation `zeta3` and refinement after singling out `0` -/

/-- The action of `ζ` on the labels of `C3`. -/
def zeta3 : Equiv.Perm (Fin 15) where
  toFun := ![1, 2, 0, 4, 5, 3, 7, 8, 6, 11, 9, 10, 14, 12, 13]
  invFun := ![2, 0, 1, 5, 3, 4, 8, 6, 7, 10, 11, 9, 13, 14, 12]
  left_inv := by decide
  right_inv := by decide

theorem keepC3_zeta3 : ∀ m, keepC3 (zeta3 m) = rhoIdx (keepC3 m) := by
  decide

theorem frameC3_zeta3 (m : Fin 15) : frameC3.p (zeta3 m) = rhoL (frameC3.p m) := by
  change pt bR uR (keepC3 (zeta3 m)) = rhoL (pt bR uR (keepC3 m))
  rw [pt_rho, keepC3_zeta3]

theorem frameC3_zeta3_pow (i : ℕ) (m : Fin 15) :
    frameC3.p ((zeta3 ^ i) m) = (rhoL ^ i) (frameC3.p m) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, LinearIsometryEquiv.coe_mul,
      Function.comp_apply, frameC3_zeta3, ih]

theorem zeta3_adj : ∀ a b, adjOf maskC3 (zeta3 a) (zeta3 b) = adjOf maskC3 a b := by
  decide

/-- The rounds of colour refinement on the contact graph of `C3`, from the constant colouring:
the second is stable, with the classes of the five orbits of `ζ`. -/
def colC3 : Fin 3 → Fin 15 → ℕ :=
  ![fun _ => 0,
    ![2, 2, 2, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1],
    ![4, 4, 4, 3, 3, 3, 0, 0, 0, 1, 1, 1, 2, 2, 2]]

theorem colC3_refines : ∀ k : Fin 2, Refines (adjOf maskC3) (colC3 k.castSucc) (colC3 k.succ) := by
  decide

theorem colC3_class0 : ∀ v, colC3 2 v = colC3 2 0 → v = 0 ∨ v = 1 ∨ v = 2 := by
  decide

/-- The rounds of colour refinement on the contact graph of `C3`, from the colouring that singles
out `0`. -/
def indC3 : Fin 4 → Fin 15 → ℕ :=
  ![fun v => if v = 0 then 1 else 0,
    ![5, 4, 4, 3, 1, 3, 2, 0, 0, 1, 1, 1, 1, 1, 1],
    ![11, 10, 10, 8, 6, 9, 7, 1, 0, 5, 4, 2, 3, 3, 3],
    ![14, 12, 13, 10, 8, 11, 9, 1, 0, 7, 6, 2, 4, 5, 3]]

theorem indC3_refines : ∀ k : Fin 3, Refines (adjOf maskC3) (indC3 k.castSucc) (indC3 k.succ) := by
  decide

theorem indC3_injective : Function.Injective (indC3 3) := by
  decide

/-- An automorphism of `listGraph S3` that fixes `0` is the identity. -/
theorem perm_S3_eq_one (σ : Equiv.Perm (Fin 15)) (hσ : ∀ a b, adjOf maskC3 (σ a) (σ b) = adjOf maskC3 a b)
    (h0 : σ 0 = 0) : σ = 1 := by
  have hcol : ∀ k : Fin 4, ∀ v, indC3 k (σ v) = indC3 k v := by
    intro k
    induction k using Fin.induction with
    | zero =>
      intro v
      show (if σ v = 0 then 1 else 0) = (if v = 0 then 1 else 0)
      have : σ v = 0 ↔ v = 0 := by
        constructor
        · intro h
          exact σ.injective (h.trans h0.symm)
        · rintro rfl
          exact h0
      simp only [this]
    | succ k ih => exact (indC3_refines k).perm hσ ih
  ext v
  exact congrArg Fin.val (indC3_injective (hcol 3 v))

/-- The automorphisms of `listGraph S3` are the powers `zeta3 ^ i`, `i < 3`. -/
theorem perm_S3_eq_zeta3_pow (σ : Equiv.Perm (Fin 15))
    (hσ : ∀ a b, (Nonunique.listGraph Nonunique.S3).Adj (σ a) (σ b) ↔
      (Nonunique.listGraph Nonunique.S3).Adj a b) : ∃ i : Fin 3, σ = zeta3 ^ (i : ℕ) := by
  have hadj := adjOf_perm listGraph_S3_adj hσ
  have hcol : ∀ k : Fin 3, ∀ v, colC3 k (σ v) = colC3 k v := by
    intro k
    induction k using Fin.induction with
    | zero => intro v; rfl
    | succ k ih => exact (colC3_refines k).perm hadj ih
  -- `τ⁻¹ * σ` preserves the adjacency for every power `τ` of `zeta3`
  have hpow : ∀ i : ℕ, ∀ a b, adjOf maskC3 ((zeta3 ^ i) a) ((zeta3 ^ i) b) = adjOf maskC3 a b := by
    intro i
    induction i with
    | zero => intro a b; rfl
    | succ i ih =>
      intro a b
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, zeta3_adj, ih]
  have hcomp : ∀ i : ℕ, ∀ a b,
      adjOf maskC3 (((zeta3 ^ i)⁻¹ * σ) a) (((zeta3 ^ i)⁻¹ * σ) b) = adjOf maskC3 a b := by
    intro i a b
    have hc : ∀ x, (zeta3 ^ i) ((zeta3 ^ i)⁻¹ x) = x := fun x => by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hpow i, hc, hc, hadj]
  have hfix : ∀ i : Fin 3, (zeta3 ^ (i : ℕ)) 0 = σ 0 → σ = zeta3 ^ (i : ℕ) := by
    intro i hi
    have h1 := perm_S3_eq_one _ (hcomp i) (by
      rw [Equiv.Perm.mul_apply, ← hi, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply])
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  rcases colC3_class0 (σ 0) (hcol 2 0) with h | h | h
  · exact ⟨0, hfix 0 (by rw [h]; rfl)⟩
  · exact ⟨1, hfix 1 (by rw [h]; rfl)⟩
  · exact ⟨2, hfix 2 (by rw [h]; rfl)⟩

/-! ## The contact graphs -/

/-- A permutation of the labels preserving the contact graph of `C1` is the identity. -/
theorem perm_C1_eq_one (σ : Equiv.Perm (Fin 15))
    (hσ : ∀ a b, (Nonunique.contactGraph frameC1.p uR).Adj (σ a) (σ b) ↔
      (Nonunique.contactGraph frameC1.p uR).Adj a b) : σ = 1 := by
  rw [Nonunique.contactGraph_C1] at hσ
  exact perm_S1_eq_one σ hσ

/-- A permutation of the labels preserving the contact graph of `C3` is a power of `zeta3`. -/
theorem perm_C3_eq_zeta3_pow (σ : Equiv.Perm (Fin 15))
    (hσ : ∀ a b, (Nonunique.contactGraph frameC3.p uR).Adj (σ a) (σ b) ↔
      (Nonunique.contactGraph frameC3.p uR).Adj a b) : ∃ i : Fin 3, σ = zeta3 ^ (i : ℕ) := by
  rw [Nonunique.contactGraph_C3] at hσ
  exact perm_S3_eq_zeta3_pow σ hσ

/-- `C1`: the only automorphism of the contact graph of `C1` is the identity. -/
theorem aut_contactGraph_C1
    (φ : Nonunique.contactGraph frameC1.p uR ≃g Nonunique.contactGraph frameC1.p uR) :
    ∀ m, φ m = m := by
  have h := perm_C1_eq_one φ.toEquiv (fun a b => φ.map_adj_iff)
  intro m
  exact congrArg (fun σ : Equiv.Perm (Fin 15) => σ m) h

/-- `C3`: the automorphisms of the contact graph of `C3` are the permutations
`p ↦ ζ^i p`, `i = 0, 1, 2`: each automorphism is one of them, and each of them is one. -/
theorem aut_contactGraph_C3 :
    (∀ φ : Nonunique.contactGraph frameC3.p uR ≃g Nonunique.contactGraph frameC3.p uR,
      ∃ i : Fin 3, ∀ m, frameC3.p (φ m) = (rhoL ^ (i : ℕ)) (frameC3.p m)) ∧
    ∀ i : Fin 3, ∃ φ : Nonunique.contactGraph frameC3.p uR ≃g Nonunique.contactGraph frameC3.p uR,
      ∀ m, frameC3.p (φ m) = (rhoL ^ (i : ℕ)) (frameC3.p m) := by
  refine ⟨fun φ => ?_, fun i => ?_⟩
  · obtain ⟨i, hi⟩ := perm_C3_eq_zeta3_pow φ.toEquiv (fun a b => φ.map_adj_iff)
    refine ⟨i, fun m => ?_⟩
    rw [← frameC3_zeta3_pow, ← hi]
    rfl
  · have hpow : ∀ j : ℕ, ∀ a b, adjOf maskC3 ((zeta3 ^ j) a) ((zeta3 ^ j) b) = adjOf maskC3 a b := by
      intro j
      induction j with
      | zero => intro a b; rfl
      | succ j ih =>
        intro a b
        rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, zeta3_adj, ih]
    refine ⟨⟨zeta3 ^ (i : ℕ), ?_⟩, fun m => frameC3_zeta3_pow i m⟩
    intro a b
    rw [Nonunique.contactGraph_C3, listGraph_S3_adj, listGraph_S3_adj]
    exact Bool.eq_iff_iff.mp (hpow i a b)

/-! ## The orthogonal maps -/

theorem pt_coord (k : Fin 18) (l : Fin 3) : (pt bR uR k).ofLp l = ptN bR uR k l / 225008 := by
  fin_cases l <;> rfl

/-- A vector orthogonal to `p_V`, `ζ p_V` and `ζ² p_V` is zero: these three points span `ℝ³`. -/
theorem eq_zero_of_inner_pV (w : E3) (h0 : ⟪w, pt bR uR 0⟫ = 0) (h1 : ⟪w, pt bR uR 1⟫ = 0)
    (h2 : ⟪w, pt bR uR 2⟫ = 0) : w = 0 := by
  have hu := uR_mem2
  have hb := bR_mem2
  obtain ⟨hA1, -⟩ := close_aN bR uR hu hb
  obtain ⟨hB1, hB2⟩ := close_bN bR uR hu hb
  obtain ⟨hC1, hC2⟩ := close_cN bR uR hu hb
  set A := aN bR uR
  set B := bN bR uR
  set C := cN bR uR
  set x := w.ofLp 0
  set y := w.ofLp 1
  set z := w.ofLp 2
  have e : ∀ k : Fin 18, ⟪w, pt bR uR k⟫ =
      (x * ptN bR uR k 0 + y * ptN bR uR k 1 + z * ptN bR uR k 2) / 225008 := by
    intro k
    simp only [PiLp.inner_apply, Fin.sum_univ_three, pt_coord, RCLike.inner_apply, conj_trivial]
    ring
  rw [e] at h0 h1 h2
  simp only [ptN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have e0 : A * x + B * y + C * z = 0 := by
    have := h0; field_simp at this; linarith
  have e1 : C * x + A * y + B * z = 0 := by
    have := h1; field_simp at this; linarith
  have e2 : B * x + C * y + A * z = 0 := by
    have := h2; field_simp at this; linarith
  have hs : 0 < A + B + C := by nlinarith
  have hsum : x + y + z = 0 := by
    have : (A + B + C) * (x + y + z) = 0 := by linear_combination e0 + e1 + e2
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have hD : 0 < (A - C) * (A - B) + (B - C) ^ 2 := by
    have h1 : 0 < A - C := by nlinarith
    have h2 : 0 < A - B := by nlinarith
    positivity
  have hx : ((A - C) * (A - B) + (B - C) ^ 2) * x = 0 := by
    linear_combination (A - B) * e0 - (B - C) * e1 + (-(A - B) * C + (B - C) * B) * hsum
  have hy : ((A - C) * (A - B) + (B - C) ^ 2) * y = 0 := by
    linear_combination (A - C) * e1 - (C - B) * e0 + (-(A - C) * B + (C - B) * C) * hsum
  have hx0 : x = 0 := (mul_eq_zero.mp hx).resolve_left hD.ne'
  have hy0 : y = 0 := (mul_eq_zero.mp hy).resolve_left hD.ne'
  have hz0 : z = 0 := by linarith
  ext l
  fin_cases l
  · exact hx0
  · exact hy0
  · exact hz0

/-- Two orthogonal maps that agree on `p_V`, `ζ p_V` and `ζ² p_V` are equal. -/
theorem linearIsometryEquiv_eq_of_pV (O O' : E3 ≃ₗᵢ[ℝ] E3)
    (h : ∀ k : Fin 18, k.val < 3 → O (pt bR uR k) = O' (pt bR uR k)) : O = O' := by
  refine LinearIsometryEquiv.ext fun v => ?_
  have hk : ∀ k : Fin 18, k.val < 3 → ⟪O'.symm (O v) - v, pt bR uR k⟫ = 0 := by
    intro k hk
    rw [inner_sub_left, ← LinearIsometryEquiv.inner_map_map O', LinearIsometryEquiv.apply_symm_apply,
      ← h k hk, LinearIsometryEquiv.inner_map_map, sub_self]
  have hw := eq_zero_of_inner_pV _ (hk 0 (by decide)) (hk 1 (by decide)) (hk 2 (by decide))
  have := congrArg O' (sub_eq_zero.mp hw)
  rwa [LinearIsometryEquiv.apply_symm_apply] at this

/-- An orthogonal map that maps the points of `X` onto themselves permutes their labels, keeping
the contact graph, when the points are distinct. -/
theorem perm_of_image_eq (X : Fin 15 → E3) (hX : Function.Injective X) (O : E3 ≃ₗᵢ[ℝ] E3)
    (hO : O '' Set.range X = Set.range X) (c : ℝ) :
    ∃ σ : Equiv.Perm (Fin 15), (∀ m, O (X m) = X (σ m)) ∧
      ∀ a b, (Nonunique.contactGraph X c).Adj (σ a) (σ b) ↔ (Nonunique.contactGraph X c).Adj a b := by
  have hex : ∀ m, ∃ m', O (X m) = X m' := by
    intro m
    have hm : O (X m) ∈ O '' Set.range X := Set.mem_image_of_mem O ⟨m, rfl⟩
    rw [hO] at hm
    obtain ⟨m', hm'⟩ := hm
    exact ⟨m', hm'.symm⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    apply hX
    apply O.injective
    rw [hf a, hf b, hab]
  let σ : Equiv.Perm (Fin 15) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, fun m => hf m, fun a b => ?_⟩
  show (σ a ≠ σ b ∧ ⟪X (σ a), X (σ b)⟫ = c) ↔ (a ≠ b ∧ ⟪X a, X b⟫ = c)
  have h1 : X (σ a) = O (X a) := (hf a).symm
  have h2 : X (σ b) = O (X b) := (hf b).symm
  rw [h1, h2, LinearIsometryEquiv.inner_map_map, σ.injective.ne_iff]

theorem frameC1_injective : Function.Injective frameC1.p := by
  have hk : Function.Injective keepC1 := by decide
  exact pt_injective.comp hk

theorem frameC3_injective : Function.Injective frameC3.p := by
  have hk : Function.Injective keepC3 := by decide
  exact pt_injective.comp hk

theorem image_range_of_perm (X : Fin 15 → E3) (O : E3 ≃ₗᵢ[ℝ] E3) (σ : Equiv.Perm (Fin 15))
    (h : ∀ m, O (X m) = X (σ m)) : O '' Set.range X = Set.range X := by
  rw [← Set.range_comp]
  have : (O ∘ X) = X ∘ σ := funext h
  rw [this, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]

/-- The only orthogonal map that maps `C1` onto `C1` is the identity. -/
theorem orthogonal_C1 (O : E3 ≃ₗᵢ[ℝ] E3) :
    O '' Set.range frameC1.p = Set.range frameC1.p ↔ O = LinearIsometryEquiv.refl ℝ E3 := by
  constructor
  · intro hO
    obtain ⟨σ, hσ, hadj⟩ := perm_of_image_eq frameC1.p frameC1_injective O hO uR
    have h1 := perm_C1_eq_one σ hadj
    apply linearIsometryEquiv_eq_of_pV
    intro k hk
    have hm : ∃ m : Fin 15, frameC1.p m = pt bR uR k := by
      refine ⟨⟨k.val, by omega⟩, ?_⟩
      show pt bR uR (keepC1 ⟨k.val, _⟩) = pt bR uR k
      congr 1
      revert k
      decide
    obtain ⟨m, hm⟩ := hm
    rw [← hm, hσ, h1]
    rfl
  · rintro rfl
    simp

/-- The orthogonal maps that map `C3` onto `C3` are `1`, `ζ` and `ζ²`. -/
theorem orthogonal_C3 (O : E3 ≃ₗᵢ[ℝ] E3) :
    O '' Set.range frameC3.p = Set.range frameC3.p ↔ ∃ i : Fin 3, O = rhoL ^ (i : ℕ) := by
  constructor
  · intro hO
    obtain ⟨σ, hσ, hadj⟩ := perm_of_image_eq frameC3.p frameC3_injective O hO uR
    obtain ⟨i, hi⟩ := perm_C3_eq_zeta3_pow σ hadj
    refine ⟨i, linearIsometryEquiv_eq_of_pV _ _ fun k hk => ?_⟩
    have hm : ∃ m : Fin 15, frameC3.p m = pt bR uR k := by
      refine ⟨⟨k.val, by omega⟩, ?_⟩
      show pt bR uR (keepC3 ⟨k.val, _⟩) = pt bR uR k
      congr 1
      revert k
      decide
    obtain ⟨m, hm⟩ := hm
    rw [← hm, hσ, hi, frameC3_zeta3_pow]
  · rintro ⟨i, rfl⟩
    exact image_range_of_perm _ _ (zeta3 ^ (i : ℕ)) fun m => (frameC3_zeta3_pow i m).symm

/-! ## Determinants -/

theorem det_mul (O O' : E3 ≃ₗᵢ[ℝ] E3) :
    LinearMap.det ((O * O').toLinearEquiv : E3 →ₗ[ℝ] E3) =
      LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) * LinearMap.det (O'.toLinearEquiv : E3 →ₗ[ℝ] E3) := by
  rw [← LinearMap.det_comp]
  rfl

theorem det_pow (O : E3 ≃ₗᵢ[ℝ] E3) (i : ℕ) :
    LinearMap.det ((O ^ i).toLinearEquiv : E3 →ₗ[ℝ] E3) =
      LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) ^ i := by
  induction i with
  | zero =>
    rw [pow_zero, pow_zero]
    exact LinearMap.det_id
  | succ i ih => rw [pow_succ, det_mul, ih, pow_succ]

theorem rhoL_pow_three : rhoL ^ 3 = 1 := by
  ext v l
  fin_cases l <;> simp [pow_succ, LinearIsometryEquiv.coe_mul, rhoL_apply]

/-- `ζ` is a rotation. -/
theorem det_rhoL : LinearMap.det (rhoL.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 := by
  have h := det_pow rhoL 3
  rw [rhoL_pow_three] at h
  have h1 : LinearMap.det ((1 : E3 ≃ₗᵢ[ℝ] E3).toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 :=
    LinearMap.det_id
  rw [h1] at h
  set d := LinearMap.det (rhoL.toLinearEquiv : E3 →ₗ[ℝ] E3)
  nlinarith [sq_nonneg (d - 1), sq_nonneg (d + 1), sq_nonneg d]

/-- The orthogonal maps that map `C1` or `C3` onto itself are rotations. -/
theorem orthogonal_det (O : E3 ≃ₗᵢ[ℝ] E3)
    (h : O '' Set.range frameC1.p = Set.range frameC1.p ∨
      O '' Set.range frameC3.p = Set.range frameC3.p) :
    LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 := by
  rcases h with h | h
  · rw [(orthogonal_C1 O).mp h]
    exact LinearMap.det_id
  · obtain ⟨i, rfl⟩ := (orthogonal_C3 O).mp h
    rw [det_pow, det_rhoL, one_pow]

end Tammes15.PaperSteps
