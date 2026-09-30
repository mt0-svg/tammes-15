import Tammes15.Draw.Defs

/-!
# Corollary k3: at most three rattlers

Each face has at least three darts and each of the `k` hexagons holding a rattler has six, the
hexagons being distinct faces, so `3F + 3k ≤ 2E`; the degrees are at least 3, so `3n ≤ 2E`;
Euler's relation gives `F + n = E + 2`; with `n + k = 15` these force `k ≤ 3` (Section 3,
Corollary k3).
-/

open Real

namespace Tammes15

open scoped Classical

/-- The cycle of `x` under a permutation has `minimalPeriod f x` elements. -/
theorem card_sameCycle_eq_minimalPeriod {D : Type} [Fintype D] (f : Equiv.Perm D) (x : D) :
    Nat.card {y // f.SameCycle x y} = Function.minimalPeriod f x := by
  have h_same_cycle_iff_orbit : ∀ y, f.SameCycle x y ↔ y ∈ MulAction.orbit (Subgroup.zpowers f) x := by
    intro y
    constructor
    · intro h
      rcases h with ⟨i, hi⟩
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨f ^ i, Subgroup.zpow_mem_zpowers f i⟩, ?_⟩
      simpa [Equiv.Perm.smul_def] using hi
    · intro h
      rw [MulAction.mem_orbit_iff] at h
      rcases h with ⟨g, hg⟩
      have hg_mem : (g : Equiv.Perm D) ∈ Subgroup.zpowers f := g.property
      rcases Subgroup.mem_zpowers_iff.mp hg_mem with ⟨i, hi⟩
      have hg_eq : (g : Equiv.Perm D) = f ^ i := hi.symm
      rw [← hg, Subgroup.smul_def, hg_eq, Equiv.Perm.smul_def]
      exact ⟨i, rfl⟩
  have h_equiv : {y // f.SameCycle x y} ≃ {y // y ∈ MulAction.orbit (Subgroup.zpowers f) x} :=
    Equiv.subtypeEquivRight h_same_cycle_iff_orbit
  have : Fintype (MulAction.orbit (Subgroup.zpowers f) x) :=
    Fintype.ofFinite _
  calc
    Nat.card {y // f.SameCycle x y} = Nat.card {y // y ∈ MulAction.orbit (Subgroup.zpowers f) x} :=
      Nat.card_congr h_equiv
    _ = Nat.card (MulAction.orbit (Subgroup.zpowers f) x) := rfl
    _ = Fintype.card (MulAction.orbit (Subgroup.zpowers f) x) := by
      rw [Nat.card_eq_fintype_card]
    _ = Function.minimalPeriod (f • ·) x := by
      rw [MulAction.minimalPeriod_eq_card]
    _ = Function.minimalPeriod f x := by
      simp [Equiv.Perm.smul_def]

/-- Counting darts by cycles: every cycle has at least three elements, and `ι` indexes distinct
cycles of six elements. -/
theorem three_mul_card_cycles_add_le {D : Type} [Fintype D] (f : Equiv.Perm D)
    (h3 : ∀ x, 3 ≤ Function.minimalPeriod f x) {ι : Type} [Fintype ι] (h : ι → D)
    (h6 : ∀ i, Function.minimalPeriod f (h i) = 6)
    (hd : ∀ i j, i ≠ j → ¬ f.SameCycle (h i) (h j)) :
    3 * Nat.card (Quotient (Equiv.Perm.SameCycle.setoid f)) + 3 * Fintype.card ι ≤
      Fintype.card D := by
  classical
    let Q := Quotient (Equiv.Perm.SameCycle.setoid f)
    let proj : D → Q := Quotient.mk (Equiv.Perm.SameCycle.setoid f)
    have hcardQ : Nat.card Q = Fintype.card Q := Nat.card_eq_fintype_card
    -- The map i ↦ proj (h i) is injective
    have hinj : Function.Injective (proj ∘ h) := by
      intro i j heq
      by_contra! hne
      apply hd i j hne
      have := (Quotient.eq (r := Equiv.Perm.SameCycle.setoid f)).mp heq
      exact this
    -- Express Fintype.card D as a sum of fiber cardinalities
    have hcardD_sum : (Fintype.card D : ℕ) = ∑ q : Q, Nat.card {x : D // proj x = q} := by
      have h_equiv : D ≃ Σ q : Q, {x : D // proj x = q} :=
        (Equiv.sigmaFiberEquiv proj).symm
      have h_card_equiv : Fintype.card D = Fintype.card (Σ q : Q, {x : D // proj x = q}) :=
        Fintype.card_congr h_equiv
      rw [h_card_equiv, Fintype.card_sigma]
      simp [Nat.card_eq_fintype_card]
    -- Helper: fiber cardinality equals minimalPeriod of a representative
    have hfiber_card_eq_minimalPeriod : ∀ (q : Q), Nat.card {x : D // proj x = q} = Function.minimalPeriod f (Quotient.out q) := by
      intro q
      let rep := Quotient.out q
      have hrep : proj rep = q := Quotient.out_eq q
      have h_eq : {x : D // proj x = q} ≃ {x : D // f.SameCycle x rep} := by
        refine
          { toFun := fun x => ⟨x.1, ?_⟩
            invFun := fun x => ⟨x.1, ?_⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        · have hxq : proj x.1 = q := x.2
          have hxq' : proj x.1 = proj rep := hxq.trans hrep.symm
          have h_sameCycle : f.SameCycle x.1 rep := (Quotient.eq (r := Equiv.Perm.SameCycle.setoid f)).mp hxq'
          exact h_sameCycle
        · have hx_same : f.SameCycle x.1 rep := x.2
          have hxq' : proj x.1 = proj rep := (Quotient.eq (r := Equiv.Perm.SameCycle.setoid f)).mpr hx_same
          exact hxq'.trans hrep
      have h_symm : Nat.card {x : D // f.SameCycle x rep} = Nat.card {x : D // f.SameCycle rep x} := by
        refine Nat.card_congr
          { toFun := fun x => ⟨x.1, (Equiv.Perm.sameCycle_comm (f := f)).mp x.2⟩
            invFun := fun x => ⟨x.1, (Equiv.Perm.sameCycle_comm (f := f)).mpr x.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [Nat.card_congr h_eq, h_symm, card_sameCycle_eq_minimalPeriod f rep]
    -- minimalPeriod is invariant under SameCycle
    have h_minimalPeriod_sameCycle : ∀ {x y : D}, f.SameCycle x y → Function.minimalPeriod f x = Function.minimalPeriod f y := by
      intro x y h
      have h_card_eq : Nat.card {z // f.SameCycle x z} = Nat.card {z // f.SameCycle y z} := by
        refine Nat.card_congr
          { toFun := fun z => ⟨z.1, h.symm.trans z.2⟩
            invFun := fun z => ⟨z.1, h.trans z.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [card_sameCycle_eq_minimalPeriod f x, card_sameCycle_eq_minimalPeriod f y] at h_card_eq
      exact h_card_eq
    -- For each q, the fiber size is at least 3
    have hfiber_ge_three : ∀ q : Q, 3 ≤ Nat.card {x : D // proj x = q} := by
      intro q
      rw [hfiber_card_eq_minimalPeriod q]
      exact h3 (Quotient.out q)
    -- For q = proj (h i), the fiber size is exactly 6
    have hfiber_eq_six : ∀ (i : ι), Nat.card {x : D // proj x = proj (h i)} = 6 := by
      intro i
      rw [hfiber_card_eq_minimalPeriod (proj (h i))]
      have h_sameCycle : f.SameCycle (Quotient.out (proj (h i))) (h i) := by
        have h_out_eq : proj (Quotient.out (proj (h i))) = proj (h i) := Quotient.out_eq (proj (h i))
        exact (Quotient.eq (r := Equiv.Perm.SameCycle.setoid f)).mp h_out_eq
      rw [h_minimalPeriod_sameCycle h_sameCycle, h6 i]
    -- Let T be the image of ι under proj ∘ h
    let T : Finset Q := Finset.image (proj ∘ h) Finset.univ
    have hTcard : T.card = Fintype.card ι := by
      simp [T, Finset.card_image_of_injective _ hinj]
    have hTsum : (∑ q ∈ T, 3 : ℕ) = 3 * Fintype.card ι := by
      simp [hTcard, mul_comm]
    have h_sum_ite : (∑ q : Q, (if q ∈ T then (3 : ℕ) else 0)) = (∑ q ∈ T, 3) := by
      calc
        (∑ q : Q, (if q ∈ T then (3 : ℕ) else 0)) = ∑ q ∈ (Finset.univ : Finset Q), (if q ∈ T then (3 : ℕ) else 0) := rfl
        _ = ∑ q ∈ (Finset.univ : Finset Q) ∩ T, (3 : ℕ) := by rw [Finset.sum_ite_mem]
        _ = ∑ q ∈ T, (3 : ℕ) := by simp
    calc
      3 * Nat.card Q + 3 * Fintype.card ι
          = 3 * Fintype.card Q + 3 * Fintype.card ι := by rw [hcardQ]
      _ = (∑ _q : Q, 3) + 3 * Fintype.card ι := by
        simp [mul_comm]
      _ = (∑ q : Q, 3) + (∑ q ∈ T, 3) := by rw [hTsum]
      _ = (∑ q : Q, 3) + (∑ q : Q, (if q ∈ T then (3 : ℕ) else 0)) := by rw [h_sum_ite]
      _ = ∑ q : Q, (3 + if q ∈ T then 3 else 0) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ q : Q, Nat.card {x : D // proj x = q} := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        by_cases hqT : q ∈ T
        · rw [if_pos hqT]
          rcases Finset.mem_image.mp hqT with ⟨i, _, hi⟩
          have hq : q = proj (h i) := hi.symm
          rw [hq]
          rw [hfiber_eq_six i]
        · rw [if_neg hqT]
          exact hfiber_ge_three q
      _ = Fintype.card D := by
        rw [hcardD_sum]

/-- The points outside the range of an embedding into `Fin N`. -/
theorem card_compl_range_add {V : Type} [Fintype V] {N : ℕ} (emb : V ↪ Fin N) :
    Fintype.card {i : Fin N // ∀ a, emb a ≠ i} + Fintype.card V = N := by
  have h_range_card : Fintype.card (Set.range emb : Set (Fin N)) = Fintype.card V :=
    Set.card_range_of_injective emb.injective
  have h_card_fin : Fintype.card (Fin N) = N := Fintype.card_fin N
  have h_equiv : {i : Fin N // ∀ a, emb a ≠ i} ≃ {i : Fin N // i ∉ (Set.range emb : Set (Fin N))} := by
    refine
    { toFun := λ ⟨i, hi⟩ => ⟨i, λ h => ?_⟩
      invFun := λ ⟨i, hi⟩ => ⟨i, λ a heq => ?_⟩
      left_inv := λ _ => rfl
      right_inv := λ _ => rfl }
    · rcases h with ⟨a, ha⟩
      exact hi a ha
    · apply hi
      exact ⟨a, heq⟩
  have h_card_compl : Fintype.card {i : Fin N // i ∉ (Set.range emb : Set (Fin N))} =
      Fintype.card (Fin N) - Fintype.card (Set.range emb : Set (Fin N)) :=
    Fintype.card_subtype_compl (λ i => i ∈ (Set.range emb : Set (Fin N)))
  have h_le : Fintype.card V ≤ N := by
    calc
      Fintype.card V ≤ Fintype.card (Fin N) := Fintype.card_le_of_embedding emb
      _ = N := h_card_fin
  calc
    Fintype.card {i : Fin N // ∀ a, emb a ≠ i} + Fintype.card V
        = Fintype.card {i : Fin N // i ∉ (Set.range emb : Set (Fin N))} + Fintype.card V := by
          rw [Fintype.card_congr h_equiv]
    _ = (Fintype.card (Fin N) - Fintype.card (Set.range emb : Set (Fin N))) + Fintype.card V := by
          rw [h_card_compl]
    _ = (N - Fintype.card V) + Fintype.card V := by rw [h_card_fin, h_range_card]
    _ = N := by omega

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Corollary k3. -/
theorem k_le_three_of_hex (k : ℕ) (hcard : Fintype.card V + k = 15) (R : RotSys G)
    (hdeg : ∀ a, 3 ≤ G.degree a) (hsph : R.Spherical)
    (hface : ∀ e, 3 ≤ Function.minimalPeriod R.face e)
    {ι : Type} [Fintype ι] (hι : Fintype.card ι = k) (hex : ι → G.Dart)
    (h6 : ∀ r, Function.minimalPeriod R.face (hex r) = 6)
    (hdist : ∀ r r', r ≠ r' → ¬ R.face.SameCycle (hex r) (hex r')) : k ≤ 3 := by
  have h1 := three_mul_card_cycles_add_le R.face hface hex h6 hdist
  rw [G.dart_card_eq_twice_card_edges, hι] at h1
  have h3 : 3 * Fintype.card V ≤ 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc 3 * Fintype.card V = ∑ _v : V, 3 := by simp [mul_comm]
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hdeg v
  have h2 := hsph
  unfold RotSys.Spherical RotSys.faceCount at h2
  omega

end Tammes15
