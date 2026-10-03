import Tammes15.TwoConn.Facets
import Tammes15.Vendor.EM8.PermutationFixedSpace

/-!
# Euler characteristic of a rotation system: genus bound and parity

For a rotation system `R` of a finite graph without isolated vertex, `V - E + F ≤ 2` when the
graph is connected (`rotSys_euler_le`, from the dimension count of the eight-point proof,
`connected_permutation_cycle_bound`, applied to the dart reversal and `R.rot.symm`, whose product
is `R.face`), and `V - E + F` is even (`rotSys_euler_even`, from the signs of the three
permutations). Used for the hull (`hull_euler`) and for the graph itself (Regions.lean) in the proof of
Corollary A.6 (paper, Lemma A.5 and Corollary A.6).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace
open Tammes15.Vendor.EM8.SquareAntiprismVerification

namespace Tammes15

open scoped Classical


-- Helper lemma: the point function at index 0 gives q.out
theorem point_zero_eq_out {α : Type*} [Finite α] (σ : Equiv.Perm α) (q : PermutationOrbit σ) :
    (orbitPermutationCycle σ q).point 0 = q.out := by
  unfold orbitPermutationCycle canonicalPermutationCycle
  have h := (Classical.choose_spec (permutation_cycle_enumeration_exists σ q.out)) 0
  -- h : (Classical.choose ...).point 0 = (⇑σ)^[0.val] (q.out)
  -- 0.val = 0, and (⇑σ)^[0] = id
  simpa using h

-- For an involution, any permutation cycle has size at most 1
theorem perm_cycle_size_le_one_of_involutive {α : Type*} (σ : Equiv.Perm α)
    (hσ : Function.Involutive σ) (C : PermutationCycle σ) : C.size ≤ 1 := by
  by_contra! h
  have hsize2 : 2 ≤ C.size := by omega
  have hcard : 2 < C.size + 1 := by omega
  let i0 : Fin (C.size + 1) := ⟨0, by omega⟩
  let i1 : Fin (C.size + 1) := ⟨1, by omega⟩
  let i2 : Fin (C.size + 1) := ⟨2, hcard⟩
  have h_add0 : i0 + 1 = i1 := by
    apply Fin.ext
    -- Goal: (i0 + 1).val = i1.val
    -- i0.val = 0, i1.val = 1
    -- (i0 + 1).val = (0 + 1) % (C.size + 1) = 1 (since 1 < C.size + 1)
    have h0 : i0.val = 0 := rfl
    have h1 : i1.val = 1 := rfl
    rw [Fin.val_add, h0, h1]
    have h_one_val : (1 : Fin (C.size + 1)).val = 1 := by
      have hpos : 1 < C.size + 1 := by omega
      simp [Nat.mod_eq_of_lt hpos]
    rw [h_one_val]
    norm_num
    -- After norm_num, the goal is 0 < C.size, which follows from h
    omega
  have h_add1 : i1 + 1 = i2 := by
    apply Fin.ext
    have h1 : i1.val = 1 := rfl
    have h2 : i2.val = 2 := rfl
    rw [Fin.val_add, h1, h2]
    have h_one_val : (1 : Fin (C.size + 1)).val = 1 := by
      have hpos : 1 < C.size + 1 := by omega
      simp [Nat.mod_eq_of_lt hpos]
    rw [h_one_val]
    norm_num
    -- After norm_num, the goal is 2 ≤ C.size, which is hsize2
    exact hsize2
  have h01 : σ (C.point i0) = C.point i1 := by
    simpa [h_add0] using C.step i0
  have h12 : σ (C.point i1) = C.point i2 := by
    simpa [h_add1] using C.step i1
  have hinv : σ (σ (C.point i0)) = C.point i0 := hσ (C.point i0)
  have h02 : C.point i0 = C.point i2 := by
    calc
      C.point i0 = σ (σ (C.point i0)) := by rw [hinv]
      _ = σ (C.point i1) := by rw [h01]
      _ = C.point i2 := by rw [h12]
  have h_eq : i0 = i2 := C.injective h02
  have h_val : (0 : ℕ) = (2 : ℕ) := by simpa using congrArg Fin.val h_eq
  omega

-- For an involution, size = 0 iff the orbit representative is a fixed point
theorem size_eq_zero_iff_fixed_point {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (_hσ : Function.Involutive σ) (q : PermutationOrbit σ) :
    (orbitPermutationCycle σ q).size = 0 ↔ σ (q.out) = q.out := by
  constructor
  · intro hsize
    have hstep0 : σ ((orbitPermutationCycle σ q).point 0) = (orbitPermutationCycle σ q).point 0 := by
      have hstep := (orbitPermutationCycle σ q).step 0
      -- In Fin (size+1) with size=0, 0+1=0
      have h_add : (0 : Fin ((orbitPermutationCycle σ q).size + 1)) + 1 = 0 := by
        rw [hsize]
        apply Fin.ext; decide
      simpa [hsize, h_add] using hstep
    simpa [point_zero_eq_out σ q] using hstep0
  · intro hfix
    by_contra! hsize
    have hsize_pos : 1 ≤ (orbitPermutationCycle σ q).size := by
      have hpos : 0 < (orbitPermutationCycle σ q).size := Nat.pos_of_ne_zero hsize
      omega
    have hcard : 1 < (orbitPermutationCycle σ q).size + 1 :=
      Nat.lt_succ_of_le hsize_pos
    let i0 : Fin ((orbitPermutationCycle σ q).size + 1) := ⟨0, by omega⟩
    let i1 : Fin ((orbitPermutationCycle σ q).size + 1) := ⟨1, hcard⟩
    have h_ne : i0 ≠ i1 := by
      intro h; have hval := congrArg Fin.val h; simp [i0, i1] at hval
    have h_iter : ∀ n : ℕ, σ^[n] (q.out) = q.out := by
      intro n
      induction' n with k ih
      · rfl
      · rw [Function.iterate_succ_apply, hfix, ih]
    have hpoint (i : Fin ((orbitPermutationCycle σ q).size + 1)) :
        (orbitPermutationCycle σ q).point i = q.out := by
      have hspec := (Classical.choose_spec (permutation_cycle_enumeration_exists σ q.out)) i
      simpa [orbitPermutationCycle, canonicalPermutationCycle, h_iter] using hspec
    have h_eq : (orbitPermutationCycle σ q).point i0 = (orbitPermutationCycle σ q).point i1 := by
      simp [hpoint]
    have := (orbitPermutationCycle σ q).injective h_eq
    exact h_ne this

-- The number of fixed-point orbits equals the number of fixed points
theorem card_fixed_point_orbits_eq_card_fixed_points {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (hσ : Function.Involutive σ) :
    (Finset.univ.filter fun q : PermutationOrbit σ => (orbitPermutationCycle σ q).size = 0).card =
    (Finset.univ.filter fun a => σ a = a).card := by
  -- Build a bijection between the two sets using Quotient.out
  let A := Finset.univ.filter fun q : PermutationOrbit σ => (orbitPermutationCycle σ q).size = 0
  let B := Finset.univ.filter fun a => σ a = a
  have hA (q : PermutationOrbit σ) (hq : q ∈ A) : σ (q.out) = q.out := by
    have hsize : (orbitPermutationCycle σ q).size = 0 := by simpa [A] using hq
    exact ((size_eq_zero_iff_fixed_point σ hσ q).mp hsize)
  have hB (a : α) (ha : a ∈ B) : σ a = a := by simpa [B] using ha
  -- Helper lemma: if σ x = x, then the SameCycle class of x is just {x}
  have h_sameCycle_singleton (x : α) (hfix : σ x = x) (y : α) :
      Equiv.Perm.SameCycle σ x y ↔ y = x := by
    have h_invol : σ (σ x) = x := hσ x
    constructor
    · intro h
      rcases h with ⟨n, hn⟩
      have h_cases := Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self h_invol n
      rcases h_cases with (h' | h')
      · -- σ ^ n x = x
        rw [h'] at hn
        exact hn.symm
      · -- σ ^ n x = σ x
        rw [h', hfix] at hn
        exact hn.symm
    · intro h; exact h.symm.sameCycle σ
  -- The map q ↦ q.out is injective on orbits
  have h_inj : Function.Injective (fun q : PermutationOrbit σ => q.out) := by
    intro q1 q2 h
    -- h : q1.out = q2.out
    have h' : q1.out = q2.out := h
    have h_mk : (Quotient.mk (permutationOrbitSetoid σ)) (q1.out) =
               (Quotient.mk (permutationOrbitSetoid σ)) (q2.out) := by rw [h']
    -- We know q1 = ⟦q1.out⟧ and q2 = ⟦q2.out⟧
    have h1 : q1 = Quotient.mk (permutationOrbitSetoid σ) (q1.out) := (Quotient.out_eq q1).symm
    have h2 : q2 = Quotient.mk (permutationOrbitSetoid σ) (q2.out) := (Quotient.out_eq q2).symm
    calc
      q1 = Quotient.mk (permutationOrbitSetoid σ) (q1.out) := h1
      _ = Quotient.mk (permutationOrbitSetoid σ) (q2.out) := by rw [h']
      _ = q2 := h2.symm
  -- The image of A under q ↦ q.out is exactly B
  have h_image : Finset.image (fun q : PermutationOrbit σ => q.out) A = B := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
      have hsize : (orbitPermutationCycle σ q).size = 0 := by simpa [A] using hq
      have hfix : σ (q.out) = q.out := ((size_eq_zero_iff_fixed_point σ hσ q).mp hsize)
      simpa [B] using hfix
    · intro x hx
      have hfix : σ x = x := by simpa [B] using hx
      let q : PermutationOrbit σ := Quotient.mk _ x
      have hqout_eq_x : q.out = x := by
        have h_same : Equiv.Perm.SameCycle σ x (q.out) := by
          -- q = ⟦x⟧, so ⟦q.out⟧ = q = ⟦x⟧
          have h_mk : (Quotient.mk (permutationOrbitSetoid σ)) (q.out) =
                     (Quotient.mk (permutationOrbitSetoid σ)) x := by
            -- q is defined as Quotient.mk _ x, so q.out = x by Quotient.out_eq
            simp [q]
          -- Quotient.exact gives SameCycle σ (q.out) x, we need SameCycle σ x (q.out)
          have h := Quotient.exact h_mk
          -- h : SameCycle σ (q.out) x
          -- SameCycle is symmetric
          exact h.symm
        exact ((h_sameCycle_singleton x hfix (q.out)).mp h_same)
      have hqA : q ∈ A := by
        have hsize := (size_eq_zero_iff_fixed_point σ hσ q).mpr ?_
        · simpa [A] using hsize
        · rw [hqout_eq_x]
          exact hfix
      apply Finset.mem_image.mpr
      exact ⟨q, hqA, hqout_eq_x⟩
  calc
    A.card = (Finset.image (fun q : PermutationOrbit σ => q.out) A).card := by
      rw [Finset.card_image_of_injective _ h_inj]
    _ = B.card := by rw [h_image]

/-- An involution has as many orbits as half the points plus half the fixed points. -/
theorem two_mul_card_orbits_involutive {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (hσ : Function.Involutive σ) :
    2 * Fintype.card (PermutationOrbit σ) =
      Fintype.card α + (Finset.univ.filter fun a => σ a = a).card := by
  -- For each orbit, the cycle size is 0 or 1
  have hsize_cases (q : PermutationOrbit σ) :
      (orbitPermutationCycle σ q).size = 0 ∨ (orbitPermutationCycle σ q).size = 1 := by
    have hle := perm_cycle_size_le_one_of_involutive σ hσ (orbitPermutationCycle σ q)
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hle) with (h | h)
    · exact Or.inl h
    · exact Or.inr h
  -- The sum equation from the given lemma
  have hsum : (∑ q : PermutationOrbit σ, ((orbitPermutationCycle σ q).size + 1)) = Fintype.card α := by
    simpa using sum_permutation_cycle_lengths σ
  -- For each orbit, 2 = (size + 1) + (1 - size) because size ∈ {0,1}
  have h_eq_term (q : PermutationOrbit σ) : (2 : ℕ) = ((orbitPermutationCycle σ q).size + 1) +
      (1 - (orbitPermutationCycle σ q).size) := by
    have hle := perm_cycle_size_le_one_of_involutive σ hσ (orbitPermutationCycle σ q)
    omega
  -- Sum both sides
  have h_sum_eq : (∑ q : PermutationOrbit σ, (2 : ℕ)) =
      (∑ q : PermutationOrbit σ, ((orbitPermutationCycle σ q).size + 1)) +
      (∑ q : PermutationOrbit σ, (1 - (orbitPermutationCycle σ q).size)) := by
    calc
      (∑ q : PermutationOrbit σ, (2 : ℕ)) = (∑ q : PermutationOrbit σ, (((orbitPermutationCycle σ q).size + 1) +
        (1 - (orbitPermutationCycle σ q).size))) := by
        apply Finset.sum_congr rfl; intro q hq; rw [h_eq_term q]
      _ = (∑ q : PermutationOrbit σ, ((orbitPermutationCycle σ q).size + 1)) +
        (∑ q : PermutationOrbit σ, (1 - (orbitPermutationCycle σ q).size)) := by
        simp [Finset.sum_add_distrib]
  -- 1 - size = 1 if size = 0, else 0
  have h_sub_term (q : PermutationOrbit σ) : 1 - (orbitPermutationCycle σ q).size =
      if (orbitPermutationCycle σ q).size = 0 then 1 else 0 := by
    have hle := perm_cycle_size_le_one_of_involutive σ hσ (orbitPermutationCycle σ q)
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hle) with (h | h)
    · rw [h]; simp
    · rw [h]; simp
  -- The second sum equals the number of orbits with size 0
  have h_sub_sum : (∑ q : PermutationOrbit σ, (1 - (orbitPermutationCycle σ q).size)) =
      (Finset.univ.filter fun q : PermutationOrbit σ => (orbitPermutationCycle σ q).size = 0).card := by
    simp [h_sub_term]
  -- The number of orbits with size 0 equals the number of fixed points
  have h_fixed_card : (Finset.univ.filter fun q : PermutationOrbit σ =>
      (orbitPermutationCycle σ q).size = 0).card =
      (Finset.univ.filter fun a => σ a = a).card :=
    card_fixed_point_orbits_eq_card_fixed_points σ hσ
  -- Assemble the final equality
  calc
    2 * Fintype.card (PermutationOrbit σ) = (∑ q : PermutationOrbit σ, (2 : ℕ)) := by
      simp [mul_comm]
    _ = (∑ q : PermutationOrbit σ, ((orbitPermutationCycle σ q).size + 1)) +
        (∑ q : PermutationOrbit σ, (1 - (orbitPermutationCycle σ q).size)) := by rw [h_sum_eq]
    _ = Fintype.card α + (∑ q : PermutationOrbit σ, (1 - (orbitPermutationCycle σ q).size)) := by rw [hsum]
    _ = Fintype.card α + (Finset.univ.filter fun q : PermutationOrbit σ =>
        (orbitPermutationCycle σ q).size = 0).card := by rw [h_sub_sum]
    _ = Fintype.card α + (Finset.univ.filter fun a => σ a = a).card := by rw [h_fixed_card]

/-- The sign of a permutation of a finite type from its number of orbits. -/
theorem sign_eq_neg_one_pow_orbits {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ =
      (-1) ^ (Fintype.card α + Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ))) := by
  set F := Fintype.card {x // σ x = x} with hF
  have hn : Fintype.card α = σ.support.card + F := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
      (fun x => σ x = x)
    rw [Finset.card_univ] at h
    rw [hF, Fintype.card_subtype, ← h, add_comm]
    rfl
  -- the orbits are the cycle factors and the fixed points
  let G : Quotient (Equiv.Perm.SameCycle.setoid σ) → (σ.cycleFactorsFinset ⊕ {x // σ x = x}) :=
    Quotient.lift (fun x => if h : σ x = x then Sum.inr ⟨x, h⟩ else
        Sum.inl ⟨σ.cycleOf x,
          Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr h)⟩)
      (by
        intro x y hxy
        change σ.SameCycle x y at hxy
        by_cases hx : σ x = x
        · obtain rfl : x = y := hxy.eq_of_left hx
          rfl
        · have hy : ¬ σ y = y := fun hy => hx (hxy.apply_eq_self_iff.mpr hy)
          simp only [dite_eq_right hx, dite_eq_right hy]
          exact congrArg Sum.inl (Subtype.ext hxy.cycleOf_eq))
  have hG : Function.Bijective G := by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with
      | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
      apply Quotient.sound
      change σ.SameCycle x y
      change (if h : σ x = x then _ else _) = (if h : σ y = y then _ else _) at hab
      by_cases hx : σ x = x <;> by_cases hy : σ y = y
      · simp only [dite_eq_left hx, dite_eq_left hy, Sum.inr.injEq, Subtype.mk.injEq] at hab
        rw [hab]
      · simp only [dite_eq_left hx, dite_eq_right hy, reduceCtorEq] at hab
      · simp only [dite_eq_right hx, dite_eq_left hy, reduceCtorEq] at hab
      · simp only [dite_eq_right hx, dite_eq_right hy, Sum.inl.injEq, Subtype.mk.injEq] at hab
        exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
          (Equiv.Perm.mem_support.mpr hx) (Equiv.Perm.mem_support.mpr hy)).mpr hab
    · rintro (⟨c, hc⟩ | ⟨x, hx⟩)
      · obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
        have haσ : σ a ≠ a :=
          Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hc ha)
        refine ⟨Quotient.mk _ a, ?_⟩
        change (if h : σ a = a then _ else _) = _
        rw [dite_eq_right haσ]
        exact congrArg Sum.inl (Subtype.ext (Equiv.Perm.cycle_is_cycleOf ha hc).symm)
      · refine ⟨Quotient.mk _ x, ?_⟩
        change (if h : σ x = x then _ else _) = _
        rw [dite_eq_left hx]
  have hQ : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) =
      σ.cycleFactorsFinset.card + F := by
    rw [Nat.card_eq_of_bijective G hG, Nat.card_sum, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType, hQ, hn, Equiv.Perm.cycleType_def,
    Multiset.card_map]
  have he : σ.support.card + F + (σ.cycleFactorsFinset.card + F) =
      (σ.support.card + Multiset.card σ.cycleFactorsFinset.val) + 2 * F := by
    rw [← Finset.card_def]
    ring
  rw [he, pow_add (-1 : ℤˣ) _ (2 * F), pow_mul, Int.units_sq, one_pow, mul_one]

section RotSys

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The reversal of darts. -/
def dartRev (G : SimpleGraph V) : Equiv.Perm G.Dart :=
  Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive

omit [Fintype V] [DecidableEq V] in
theorem dartRev_apply (d : G.Dart) : dartRev G d = d.symm := rfl

theorem RotSys.face_eq_trans (R : RotSys G) : R.face = (dartRev G).trans R.rot.symm := rfl

theorem RotSys.faceCount_eq_card (R : RotSys G) :
    R.faceCount = Fintype.card (PermutationOrbit R.face) := by
  unfold RotSys.faceCount PermutationOrbit
  have h_eq : (Quotient (Equiv.Perm.SameCycle.setoid R.face)) ≃
      (Quotient (Tammes15.Vendor.EM8.SquareAntiprismVerification.permutationOrbitSetoid R.face)) :=
    Quotient.congr (Equiv.refl _) (fun _ _ => Iff.rfl)
  rw [Nat.card_congr h_eq, Nat.card_eq_fintype_card]

theorem card_orbits_dartRev :
    Fintype.card (PermutationOrbit (dartRev G)) = G.edgeFinset.card := by
  have h := two_mul_card_orbits_involutive (dartRev G) SimpleGraph.Dart.symm_involutive
  rw [Finset.filter_eq_empty_iff.mpr (fun d _ => by simp [dartRev_apply, SimpleGraph.Dart.symm_ne]),
    Finset.card_empty, add_zero, SimpleGraph.dart_card_eq_twice_card_edges] at h
  omega

theorem RotSys.card_orbits_rot_symm (R : RotSys G) (hne : ∀ v, ∃ w, G.Adj v w) :
    Fintype.card (PermutationOrbit R.rot.symm) = Fintype.card V := by
  -- R.rot.symm preserves fst because R.rot does
  have h_rot_symm_fst : ∀ x : G.Dart, (R.rot.symm x).fst = x.fst := by
    intro x
    have h := R.rot_fst (R.rot.symm x)
    -- h : (R.rot (R.rot.symm x)).fst = (R.rot.symm x).fst
    -- but R.rot (R.rot.symm x) = x
    simpa [Equiv.apply_symm_apply] using h.symm
  -- R.rot also preserves fst
  have h_inv_fst : ∀ x : G.Dart, (R.rot x).fst = x.fst := R.rot_fst
  -- SameCycle for R.rot.symm implies equality of fst
  have h_sameCycle_fst : ∀ {x y : G.Dart}, Equiv.Perm.SameCycle R.rot.symm x y → x.fst = y.fst := by
    intro x y h
    rcases h with ⟨i, hi⟩
    -- hi : (R.rot.symm ^ i) x = y
    -- We show that for all i : ℤ, ((R.rot.symm ^ i) x).fst = x.fst
    have h_pow_fst : ∀ (i : ℤ) (x : G.Dart), ((R.rot.symm ^ i) x).fst = x.fst := by
      intro i x
      induction' i using Int.induction_on with n ih n ih
      · rfl
      · -- i = (n : ℤ) + 1
        have h_eq : (R.rot.symm ^ ((n : ℤ) + 1)) x = R.rot.symm ((R.rot.symm ^ (n : ℤ)) x) := by
          calc
            (R.rot.symm ^ ((n : ℤ) + 1)) x = ((R.rot.symm ^ (n : ℤ)) * (R.rot.symm ^ (1 : ℤ))) x := by rw [zpow_add]
            _ = ((R.rot.symm ^ (n : ℤ)) * R.rot.symm) x := by simp
            _ = (R.rot.symm * (R.rot.symm ^ (n : ℤ))) x := by
              rw [(Commute.self_zpow R.rot.symm (n : ℤ)).eq]
            _ = R.rot.symm ((R.rot.symm ^ (n : ℤ)) x) := rfl
        rw [h_eq, h_rot_symm_fst, ih]
      · -- i = -(n : ℤ) - 1
        have h_eq : (R.rot.symm ^ (-(n : ℤ) - 1)) x = R.rot ((R.rot.symm ^ (-(n : ℤ))) x) := by
          calc
            (R.rot.symm ^ (-(n : ℤ) - 1)) x = (R.rot.symm ^ ((-(n : ℤ)) + (-1 : ℤ))) x := by ring_nf
            _ = ((R.rot.symm ^ (-(n : ℤ))) * (R.rot.symm ^ (-1 : ℤ))) x := by rw [zpow_add]
            _ = ((R.rot.symm ^ (-(n : ℤ))) * R.rot) x := by simp
            _ = (R.rot * (R.rot.symm ^ (-(n : ℤ)))) x := by
              have h_comm := ((Commute.refl R.rot.symm).zpow_zpow (-(n : ℤ)) (-1 : ℤ)).eq
              -- h_comm : R.rot.symm^(-n) * R.rot.symm^(-1) = R.rot.symm^(-1) * R.rot.symm^(-n)
              -- i.e., R.rot.symm^(-n) * R.rot = R.rot * R.rot.symm^(-n)
              simpa [Equiv.Perm.mul_apply] using congrArg (fun f => f x) h_comm
            _ = R.rot ((R.rot.symm ^ (-(n : ℤ))) x) := rfl
        rw [h_eq, h_inv_fst, ih]
    rw [← hi, h_pow_fst i x]
  -- Define the map from orbits to vertices
  set f : PermutationOrbit R.rot.symm → V := fun q => q.out.fst
  have h_inj : Function.Injective f := by
    intro q₁ q₂ h
    -- h : f q₁ = f q₂, i.e., q₁.out.fst = q₂.out.fst
    have h_fst : q₁.out.fst = q₂.out.fst := h
    -- By rot_cycle, R.rot.SameCycle q₁.out q₂.out
    have h_cycle : R.rot.SameCycle q₁.out q₂.out := R.rot_cycle _ _ h_fst
    -- Convert to R.rot.symm.SameCycle
    have h_cycle_symm : Equiv.Perm.SameCycle R.rot.symm q₁.out q₂.out := h_cycle.inv
    -- Therefore ⟦q₁.out⟧ = ⟦q₂.out⟧ by Quotient.sound
    have h_eq : ⟦q₁.out⟧ = ⟦q₂.out⟧ :=
      Quotient.sound (s := permutationOrbitSetoid R.rot.symm) h_cycle_symm
    -- And ⟦q⟧.out = q for any quotient element
    calc
      q₁ = ⟦q₁.out⟧ := (Quotient.out_eq q₁).symm
      _ = ⟦q₂.out⟧ := h_eq
      _ = q₂ := Quotient.out_eq q₂
  have h_surj : Function.Surjective f := by
    intro v
    -- Get a dart at vertex v
    rcases hne v with ⟨w, h_adj⟩
    let d : G.Dart := ⟨(v, w), h_adj⟩
    -- The orbit of d maps to v
    refine ⟨⟦d⟧, ?_⟩
    -- Need to show (⟦d⟧).out.fst = v
    -- Quotient.mk_out d gives the setoid relation, which is Equiv.Perm.SameCycle R.rot.symm
    have h_out_rel : Equiv.Perm.SameCycle R.rot.symm ⟦d⟧.out d :=
      Quotient.mk_out (s := permutationOrbitSetoid R.rot.symm) d
    -- By h_sameCycle_fst, ⟦d⟧.out.fst = d.fst
    have h_fst_eq : ⟦d⟧.out.fst = d.fst := h_sameCycle_fst h_out_rel
    -- And d.fst = v by construction
    simpa [d] using h_fst_eq
  -- Now we have a bijection, so the cardinalities are equal
  exact Fintype.card_congr (Equiv.ofBijective f ⟨h_inj, h_surj⟩)

/-- A function on darts invariant under reversal and rotation is constant on a connected
graph. -/
theorem RotSys.invariant_const (R : RotSys G) (hconn : G.Connected) (f : G.Dart → ℝ)
    (hrev : ∀ d, f (dartRev G d) = f d) (hrot : ∀ d, f (R.rot.symm d) = f d) (d e : G.Dart) :
    f d = f e := by
  -- Lemma: f is constant on darts with the same fst
  have hsame_fst : ∀ (d' e' : G.Dart), d'.fst = e'.fst → f d' = f e' := by
    intro d' e' hfst
    have hcycle : R.rot.SameCycle d' e' := R.rot_cycle d' e' hfst
    have hcycle_inv : Equiv.Perm.SameCycle (R.rot.symm) d' e' :=
      (Equiv.Perm.sameCycle_inv (f := R.rot)).mpr hcycle
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hcycle_inv
    -- hn : (R.rot.symm ^ n) d' = e'
    -- Goal: f d' = f e'
    -- First prove by induction on n: f d' = f ((R.rot.symm ^ n) d')
    have h_pow : ∀ n : ℕ, f d' = f ((R.rot.symm ^ n) d') := by
      intro n
      induction' n with k IH
      · rfl
      · rw [pow_succ']
        simp [hrot, IH]
    rw [h_pow n, hn]
  -- Use connectivity to propagate along walks
  have h_reach : G.Reachable (d.fst) (e.fst) := hconn (d.fst) (e.fst)
  let p : G.Walk (d.fst) (e.fst) := Classical.choice h_reach
  -- Helper: propagate f from a dart at the start of a walk to some dart at the end
  have hwalk : ∃ (e' : G.Dart), e'.fst = e.fst ∧ f d = f e' := by
    -- Use Walk.rec with a carefully chosen motive
    let motive : (u v : V) → G.Walk u v → Prop := fun u v p =>
      ∀ (d' : G.Dart), d'.fst = u → ∃ (e' : G.Dart), e'.fst = v ∧ f d' = f e'
    have h_nil : ∀ {u}, motive u u SimpleGraph.Walk.nil := by
      intro u d' hd'
      refine ⟨d', ?_, rfl⟩
      rw [hd']
    have h_cons : ∀ {u v w : V} (h : G.Adj u v) (p' : G.Walk v w),
        motive v w p' → motive u w (SimpleGraph.Walk.cons h p') := by
      intro u v w h p' ih d' hd'
      -- hd' : d'.fst = u
      -- Create dart for edge u → v
      let d1 : G.Dart := ⟨(u, v), h⟩
      have hd1_fst : d1.fst = u := rfl
      -- f d' = f d1 by hsame_fst
      have h1 : f d' = f d1 := hsame_fst d' d1 (by rw [hd', hd1_fst])
      -- f d1 = f d1.symm by hrev
      have h2 : f d1 = f d1.symm := by
        simpa [dartRev] using (hrev d1).symm
      -- d1.symm is at v
      have h_symm_fst : d1.symm.fst = v := rfl
      -- Apply IH to d1.symm
      obtain ⟨e', he'_fst, h_eq⟩ := ih d1.symm h_symm_fst
      -- h_eq : f d1.symm = f e'
      refine ⟨e', he'_fst, ?_⟩
      rw [h1, h2, h_eq]
    -- Now apply Walk.rec
    have h_result : motive (d.fst) (e.fst) p :=
      SimpleGraph.Walk.rec (motive := motive) h_nil h_cons p
    exact h_result d rfl
  obtain ⟨e', he'_fst, h_eq⟩ := hwalk
  -- h_eq : f d = f e'
  -- he'_fst : e'.fst = e.fst
  -- By hsame_fst, f e' = f e
  have h_final : f e' = f e := hsame_fst e' e (by rw [he'_fst])
  rw [h_eq, h_final]

/-- The genus bound: `V - E + F ≤ 2` for a connected rotation system without isolated vertex. -/
theorem rotSys_euler_le [Nonempty V] (R : RotSys G) (hconn : G.Connected)
    (hne : ∀ v, ∃ w, G.Adj v w) :
    (Fintype.card V : ℤ) - G.edgeFinset.card + R.faceCount ≤ 2 := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w, hw⟩ := hne v
  have h := connected_permutation_cycle_bound (dartRev G) R.rot.symm ⟨(v, w), hw⟩
    (fun f hrev hrot d e => R.invariant_const hconn (fun d => f d) hrev hrot d e)
  rw [R.card_orbits_rot_symm hne, card_orbits_dartRev,
    ← R.face_eq_trans, ← R.faceCount_eq_card, SimpleGraph.dart_card_eq_twice_card_edges] at h
  omega

/-- Parity: `V - E + F` is even for a rotation system without isolated vertex. -/
theorem rotSys_euler_even (R : RotSys G) (hne : ∀ v, ∃ w, G.Adj v w) :
    Even ((Fintype.card V : ℤ) - G.edgeFinset.card + R.faceCount) := by
  set D := Fintype.card G.Dart
  set E := G.edgeFinset.card
  set Vc := Fintype.card V
  set F := R.faceCount
  have hD_twice_E : D = 2 * E := SimpleGraph.dart_card_eq_twice_card_edges G
  have hface_eq : R.face = (dartRev G).trans R.rot.symm := RotSys.face_eq_trans R
  -- Apply sign to both sides
  have hsign_eq : Equiv.Perm.sign R.face = Equiv.Perm.sign ((dartRev G).trans R.rot.symm) := by rw [hface_eq]
  rw [Equiv.Perm.sign_trans] at hsign_eq
  -- hsign_eq : sign R.face = sign (R.rot.symm) * sign (dartRev G)
  -- Get sign formulas
  have hsign_face : Equiv.Perm.sign R.face = (-1) ^ (D + Nat.card (Quotient (Equiv.Perm.SameCycle.setoid R.face))) :=
    sign_eq_neg_one_pow_orbits R.face
  have hsign_dartRev : Equiv.Perm.sign (dartRev G) = (-1) ^ (D + Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (dartRev G)))) :=
    sign_eq_neg_one_pow_orbits (dartRev G)
  have hsign_rotsymm : Equiv.Perm.sign (R.rot.symm) = (-1) ^ (D + Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (R.rot.symm)))) :=
    sign_eq_neg_one_pow_orbits (R.rot.symm)
  rw [hsign_face, hsign_dartRev, hsign_rotsymm] at hsign_eq
  -- Relate Nat.card to the expected counts
  -- The setoids Equiv.Perm.SameCycle.setoid and permutationOrbitSetoid are equal
  have h_setoid_face : Equiv.Perm.SameCycle.setoid R.face = permutationOrbitSetoid R.face := by
    ext x y; rfl
  have h_setoid_dartRev : Equiv.Perm.SameCycle.setoid (dartRev G) = permutationOrbitSetoid (dartRev G) := by
    ext x y; rfl
  have h_setoid_rotsymm : Equiv.Perm.SameCycle.setoid (R.rot.symm) = permutationOrbitSetoid (R.rot.symm) := by
    ext x y; rfl
  have hF_card : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid R.face)) = F := by
    rw [h_setoid_face, Nat.card_eq_fintype_card]
    simpa [F] using (RotSys.faceCount_eq_card R).symm
  have hE_card : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (dartRev G))) = E := by
    rw [h_setoid_dartRev, Nat.card_eq_fintype_card]
    simpa [PermutationOrbit, E] using card_orbits_dartRev (G := G)
  have hV_card : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (R.rot.symm))) = Vc := by
    rw [h_setoid_rotsymm, Nat.card_eq_fintype_card]
    simpa [PermutationOrbit, Vc] using RotSys.card_orbits_rot_symm R hne
  rw [hF_card, hE_card, hV_card] at hsign_eq
  -- hsign_eq : (-1)^(D+F) = (-1)^(D+E) * (-1)^(D+V)
  -- Simplify RHS: (-1)^(D+E) * (-1)^(D+V) = (-1)^((D+E)+(D+V))
  have h_pow_mul : ∀ (a b : ℕ), ((-1 : ℤˣ) ^ a) * ((-1 : ℤˣ) ^ b) = (-1 : ℤˣ) ^ (a + b) := by
    intro a b
    simpa [add_comm] using (pow_add (-1 : ℤˣ) a b).symm
  rw [mul_comm ((-1 : ℤˣ) ^ (D+Vc)) ((-1 : ℤˣ) ^ (D+E)), h_pow_mul (D+E) (D+Vc)] at hsign_eq
  -- hsign_eq : (-1)^(D+F) = (-1)^((D+E)+(D+Vc))
  have h_sum : (D+E)+(D+Vc) = 2*D + E + Vc := by omega
  rw [h_sum] at hsign_eq
  -- hsign_eq : (-1)^(D+F) = (-1)^(2*D+E+V)
  -- (-1)^(2*D) = 1 since 2*D is even
  have h_even_2D : Even (2*D : ℕ) := by
    refine ⟨D, ?_⟩
    ring
  have h_neg_one_2D : ((-1 : ℤˣ) ^ (2*D : ℕ)) = (1 : ℤˣ) :=
    Even.neg_one_pow h_even_2D
  -- (-1)^(2*D+E+V) = (-1)^(2*D) * (-1)^(E+V) = 1 * (-1)^(E+V) = (-1)^(E+V)
  have h_pow_add' : ∀ (a b : ℕ), (-1 : ℤˣ) ^ (a + b) = ((-1 : ℤˣ) ^ a) * ((-1 : ℤˣ) ^ b) := by
    intro a b
    simpa [add_comm] using pow_add (-1 : ℤˣ) a b
  rw [add_assoc, h_pow_add' (2*D) (E+Vc)] at hsign_eq
  rw [h_neg_one_2D, one_mul] at hsign_eq
  -- hsign_eq : (-1)^(D+F) = (-1)^(E+V)
  -- Deduce Even (D+F) ↔ Even (E+Vc)
  have h_ne : (-1 : ℤˣ) ≠ 1 := by norm_num
  have h_parity : Even (D+F : ℕ) ↔ Even (E+Vc : ℕ) := by
    constructor
    · intro h_even
      have h_one : (-1 : ℤˣ) ^ (E+Vc : ℕ) = (1 : ℤˣ) := by
        rw [← hsign_eq]
        exact (neg_one_pow_eq_one_iff_even h_ne).mpr h_even
      exact (neg_one_pow_eq_one_iff_even h_ne).mp h_one
    · intro h_even
      have h_one : (-1 : ℤˣ) ^ (D+F : ℕ) = (1 : ℤˣ) := by
        rw [hsign_eq]
        exact (neg_one_pow_eq_one_iff_even h_ne).mpr h_even
      exact (neg_one_pow_eq_one_iff_even h_ne).mp h_one
  -- Since D = 2*E, Even (D+F) ↔ Even F
  have h_parity_F : Even (F : ℕ) ↔ Even (E+Vc : ℕ) := by
    rw [← h_parity, hD_twice_E]
    rw [Nat.even_add]
    have h_even_2E : Even (2*E : ℕ) := ⟨E, by ring⟩
    simp [h_even_2E]
  -- Convert to ℤ
  have h_parity_F_int : Even (F : ℤ) ↔ Even ((E : ℤ) + (Vc : ℤ)) := by
    rw [Int.even_coe_nat F, ← Nat.cast_add, Int.even_coe_nat (E+Vc)]
    exact h_parity_F
  -- Now Even (F + (E+V)) in ℤ
  have h_even_sum : Even ((F : ℤ) + ((E : ℤ) + (Vc : ℤ))) := by
    rw [Int.even_add]
    exact h_parity_F_int
  -- Rewrite: F + (E+V) = (Vc - E + F) + 2*E
  have h_target : Even ((Vc : ℤ) - (E : ℤ) + (F : ℤ)) := by
    have h_eq : (F : ℤ) + ((E : ℤ) + (Vc : ℤ)) = ((Vc : ℤ) - (E : ℤ) + (F : ℤ)) + 2*(E : ℤ) := by ring
    rw [h_eq] at h_even_sum
    have h_iff := (Int.even_add (m := (Vc : ℤ) - (E : ℤ) + (F : ℤ)) (n := 2*(E : ℤ))).mp h_even_sum
    have h_even_2E : Even (2*(E : ℤ)) := ⟨E, by ring⟩
    exact h_iff.mpr h_even_2E
  -- (Vc : ℤ) - (E : ℤ) + (F : ℤ) = (Fintype.card V : ℤ) - G.edgeFinset.card + R.faceCount
  simpa [Vc, E, F] using h_target

end RotSys

end Tammes15
