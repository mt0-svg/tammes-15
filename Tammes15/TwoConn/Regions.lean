import Tammes15.TwoConn.Blocks

/-!
# Regions: the faces of the graph as unions of facets

Lemmas G1 to G12 of the proof of Corollary twoconn by the convex hull (paper, Section 3,
Lemma hull and Corollary twoconn), with the cycle space bound G7 replaced by the dimension
count of the eight-point proof. Facets of the hull are adjacent across hull edges that are not
edges of `G`, and a region is a connected component of this adjacency (`regionGraph`). The
permutation `tauPerm` (reverse the hull darts that are not darts of `G`, then take the face map
of the hull rotation `rho`) preserves regions and runs from a dart of `G` to its successor on
its face (`tau_block`). Counting the orbits of the three permutations as in the genus bound,
with one invariant function per region (`euler_bound_regions`), against the positive excess of
the facets of each region (`region_chi`), gives: one face of `G` per region, Euler's relation
for `G` and connectivity of `G`.
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace
open Tammes15.Vendor.EM8.SquareAntiprismVerification

namespace Tammes15

open scoped Classical

/-! ## Counting orbits -/

/-- The dimension count of the eight-point genus bound, with the classes of a partition on which
every jointly invariant function is constant in place of connectivity. -/
theorem permutation_cycle_bound_classes {α β : Type*} [Fintype α] [Fintype β]
    (e f : Equiv.Perm α) (c : α → β)
    (hconst : ∀ v : α → ℝ, (∀ i, v (e i) = v i) → (∀ i, v (f i) = v i) →
      ∀ i j, c i = c j → v i = v j) :
    Fintype.card (PermutationOrbit e) + Fintype.card (PermutationOrbit f) +
      Fintype.card (PermutationOrbit (e.trans f)) ≤ Fintype.card α + 2 * Fintype.card β := by
  have h_dim := permutation_cycle_dimension_bound e f
  let K := isometryFixed (permutationIsometry e) ⊓ isometryFixed (permutationIsometry f)
  by_cases hne : Nonempty α
  · have := hne
    have h_finrank : Module.finrank ℝ K ≤ Fintype.card β := by
      let ev : K →ₗ[ℝ] (β → ℝ) := {
        toFun := fun v b => v.val (Function.invFun c b)
        map_add' := by
          intro v w
          ext b
          rfl
        map_smul' := by
          intro t v
          ext b
          rfl
      }
      have hinj : Function.Injective ev := by
        intro v w h
        dsimp [ev] at h
        have h_eq : ∀ i, v.val i = w.val i := by
          intro i
          have hc_eq : c i = c (Function.invFun c (c i)) := by
            symm; exact Function.invFun_eq ⟨i, rfl⟩
          have h_v_fixed_e : ∀ i, v.val (e i) = v.val i := by
            intro j
            have h_eq' := congrArg (fun (x : EuclideanSpace ℝ α) => x j) v.property.1
            dsimp [permutationIsometry, permutationLinearMap] at h_eq' ⊢
            exact h_eq'
          have h_v_fixed_f : ∀ i, v.val (f i) = v.val i := by
            intro j
            have h_eq' := congrArg (fun (x : EuclideanSpace ℝ α) => x j) v.property.2
            dsimp [permutationIsometry, permutationLinearMap] at h_eq' ⊢
            exact h_eq'
          have h_w_fixed_e : ∀ i, w.val (e i) = w.val i := by
            intro j
            have h_eq' := congrArg (fun (x : EuclideanSpace ℝ α) => x j) w.property.1
            dsimp [permutationIsometry, permutationLinearMap] at h_eq' ⊢
            exact h_eq'
          have h_w_fixed_f : ∀ i, w.val (f i) = w.val i := by
            intro j
            have h_eq' := congrArg (fun (x : EuclideanSpace ℝ α) => x j) w.property.2
            dsimp [permutationIsometry, permutationLinearMap] at h_eq' ⊢
            exact h_eq'
          have h_v_on_fiber := hconst v.val h_v_fixed_e h_v_fixed_f i (Function.invFun c (c i)) hc_eq
          have h_w_on_fiber := hconst w.val h_w_fixed_e h_w_fixed_f i (Function.invFun c (c i)) hc_eq
          have h_ev := congrFun h (c i)
          rw [h_v_on_fiber, h_w_on_fiber, h_ev]
        ext i
        exact h_eq i
      have h_finrank_le := LinearMap.finrank_le_finrank_of_injective hinj
      have h_finrank_fun : Module.finrank ℝ (β → ℝ) = Fintype.card β :=
        Module.finrank_fintype_fun_eq_card ℝ
      linarith
    linarith
  · have : IsEmpty α := not_nonempty_iff.mp hne
    simp


/-- A finite set with a fixed point free involution has even cardinality. -/
theorem even_card_of_involution {α : Type*} (s : Finset α) (f : α → α)
    (hf : ∀ a ∈ s, f a ∈ s) (hinv : ∀ a ∈ s, f (f a) = a) (hfix : ∀ a ∈ s, f a ≠ a) :
    Even s.card := by
  -- Strong induction on s.card
  have h_main : ∀ n, (∀ m < n, ∀ (t : Finset α), t.card = m → (∀ a ∈ t, f a ∈ t) → (∀ a ∈ t, f (f a) = a) → (∀ a ∈ t, f a ≠ a) → Even t.card) →
    ∀ (t : Finset α), t.card = n → (∀ a ∈ t, f a ∈ t) → (∀ a ∈ t, f (f a) = a) → (∀ a ∈ t, f a ≠ a) → Even t.card := by
    intro n ih t hcard hmap hinv_t hfix_t
    by_cases hempty : t = ∅
    · subst hempty
      refine ⟨0, ?_⟩
      simp
    · have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨a, ha⟩ := hne
      have hfa : f a ∈ t := hmap a ha
      have hfa_ne_a : f a ≠ a := hfix_t a ha
      -- s' = t \ {a, f a}
      let s' := (t.erase a).erase (f a)
      have hfa_mem_erase_a : f a ∈ t.erase a :=
        Finset.mem_erase.mpr ⟨hfa_ne_a, hfa⟩
      have hcard_erase_a : (t.erase a).card + 1 = t.card :=
        Finset.card_erase_add_one ha
      have hcard_s' : s'.card + 1 = (t.erase a).card :=
        Finset.card_erase_add_one hfa_mem_erase_a
      have hcard_total : s'.card + 2 = t.card := by
        linarith
      have hcard_lt : s'.card < t.card := by
        omega
      have hcard_lt_n : s'.card < n := by
        rw [← hcard]
        exact hcard_lt
      have hf_s' : ∀ b ∈ s', f b ∈ s' := by
        intro b hb
        rcases Finset.mem_erase.mp hb with ⟨hb_ne_fa, hb_mem⟩
        rcases Finset.mem_erase.mp hb_mem with ⟨hb_ne_a, hb_t⟩
        have hfb_t : f b ∈ t := hmap b hb_t
        have hfb_ne_a : f b ≠ a := by
          intro h
          apply hb_ne_fa
          calc
            b = f (f b) := (hinv_t b hb_t).symm
            _ = f a := by rw [h]
        have hfb_ne_fa : f b ≠ f a := by
          intro h
          apply hb_ne_a
          calc
            b = f (f b) := (hinv_t b hb_t).symm
            _ = f (f a) := by rw [h]
            _ = a := hinv_t a ha
        exact Finset.mem_erase.mpr ⟨hfb_ne_fa, Finset.mem_erase.mpr ⟨hfb_ne_a, hfb_t⟩⟩
      have hinv_s' : ∀ b ∈ s', f (f b) = b := by
        intro b hb
        rcases Finset.mem_erase.mp hb with ⟨_, hb_mem⟩
        rcases Finset.mem_erase.mp hb_mem with ⟨_, hb_t⟩
        exact hinv_t b hb_t
      have hfix_s' : ∀ b ∈ s', f b ≠ b := by
        intro b hb
        rcases Finset.mem_erase.mp hb with ⟨_, hb_mem⟩
        rcases Finset.mem_erase.mp hb_mem with ⟨_, hb_t⟩
        exact hfix_t b hb_t
      rcases ih s'.card hcard_lt_n s' rfl hf_s' hinv_s' hfix_s' with ⟨k, hk⟩
      rw [← hcard_total, hk]
      refine ⟨k + 1, ?_⟩
      ring
  exact @Nat.strong_induction_on (λ n => ∀ (t : Finset α), t.card = n → (∀ a ∈ t, f a ∈ t) → (∀ a ∈ t, f (f a) = a) → (∀ a ∈ t, f a ≠ a) → Even t.card) s.card h_main s rfl hf hinv hfix

/-! ## Regions -/

section Regions

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V → E3)

/-- Reverse the hull darts that are not darts of `G`. -/
noncomputable def revN : Equiv.Perm (hullGraph x).Dart :=
  Function.Involutive.toPerm (fun d => if G.Adj d.fst d.snd then d else d.symm) (by
    intro d
    by_cases h : G.Adj d.fst d.snd
    · simp [h]
    · have h' : ¬ G.Adj d.snd d.fst := fun h'' => h h''.symm
      simp [h, h'])

omit [Fintype V] [DecidableEq V] in
theorem revN_of_adj {d : (hullGraph x).Dart} (h : G.Adj d.fst d.snd) : revN G x d = d := by
  show (if G.Adj d.fst d.snd then d else d.symm) = d
  simp only [h, ↓reduceIte]

omit [Fintype V] [DecidableEq V] in
theorem revN_of_not_adj {d : (hullGraph x).Dart} (h : ¬ G.Adj d.fst d.snd) :
    revN G x d = d.symm := by
  show (if G.Adj d.fst d.snd then d else d.symm) = d.symm
  simp only [h, ↓reduceIte]

variable (rho : RotSys (hullGraph x))

/-- Reverse the darts off `G`, then take the face map of the hull rotation. -/
noncomputable def tauPerm : Equiv.Perm (hullGraph x).Dart := (revN G x).trans rho.face

theorem tauPerm_apply (d : (hullGraph x).Dart) : tauPerm G x rho d = rho.face (revN G x d) :=
  rfl

/-- The facet of a hull dart. -/
def facetOf (d : (hullGraph x).Dart) : PermutationOrbit rho.face :=
  Quotient.mk (permutationOrbitSetoid rho.face) d

/-- Facets adjacent across a hull edge that is not an edge of `G`. -/
def regionGraph : SimpleGraph (PermutationOrbit rho.face) :=
  SimpleGraph.fromRel fun f f' => ∃ d : (hullGraph x).Dart,
    facetOf x rho d = f ∧ facetOf x rho d.symm = f' ∧ ¬ G.Adj d.fst d.snd

/-- The region of a hull dart: the component of its facet. -/
noncomputable def region (d : (hullGraph x).Dart) : (regionGraph G x rho).ConnectedComponent :=
  (regionGraph G x rho).connectedComponentMk (facetOf x rho d)

theorem facetOf_face (d : (hullGraph x).Dart) : facetOf x rho (rho.face d) = facetOf x rho d :=
  Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

theorem region_face (d : (hullGraph x).Dart) :
    region G x rho (rho.face d) = region G x rho d := by
  rw [region, region, facetOf_face]

theorem region_symm {d : (hullGraph x).Dart} (h : ¬ G.Adj d.fst d.snd) :
    region G x rho d.symm = region G x rho d := by
  by_cases hf : facetOf x rho d.symm = facetOf x rho d
  · rw [region, region, hf]
  · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    rw [regionGraph, SimpleGraph.fromRel_adj]
    exact ⟨hf, Or.inr ⟨d, rfl, rfl, h⟩⟩

theorem region_revN (d : (hullGraph x).Dart) :
    region G x rho (revN G x d) = region G x rho d := by
  by_cases h : G.Adj d.fst d.snd
  · rw [revN_of_adj G x h]
  · rw [revN_of_not_adj G x h, region_symm G x rho h]

theorem region_tau (d : (hullGraph x).Dart) :
    region G x rho (tauPerm G x rho d) = region G x rho d := by
  rw [tauPerm_apply, region_face, region_revN]

theorem region_tau_pow (d : (hullGraph x).Dart) (n : ℕ) :
    region G x rho ((tauPerm G x rho ^ n) d) = region G x rho d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, region_tau, ih]

/-- A function invariant under `revN` and the face map is constant on each region. -/
theorem region_const (φ : (hullGraph x).Dart → ℝ) (hrev : ∀ d, φ (revN G x d) = φ d)
    (hface : ∀ d, φ (rho.face d) = φ d) (d d' : (hullGraph x).Dart)
    (h : region G x rho d = region G x rho d') : φ d = φ d' := by
  have hpow : ∀ (n : ℕ) (e : (hullGraph x).Dart), φ ((rho.face ^ n) e) = φ e := by
    intro n
    induction n with
    | zero => intro e; rfl
    | succ n ih => intro e; rw [pow_succ', Equiv.Perm.mul_apply, hface, ih]
  have hsc : ∀ e e' : (hullGraph x).Dart, facetOf x rho e = facetOf x rho e' → φ e = φ e' := by
    intro e e' hee
    have hs : rho.face.SameCycle e e' := Quotient.exact hee
    obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
    rw [← hn, hpow]
  let ψ : PermutationOrbit rho.face → ℝ := fun f => φ f.out
  have hψ : ∀ e, ψ (facetOf x rho e) = φ e := fun e =>
    hsc _ _ (Quotient.out_eq (facetOf x rho e))
  have hadj : ∀ f f', (regionGraph G x rho).Adj f f' → ψ f = ψ f' := by
    intro f f' hff
    rw [regionGraph, SimpleGraph.fromRel_adj] at hff
    obtain ⟨-, ⟨e, rfl, rfl, he⟩ | ⟨e, rfl, rfl, he⟩⟩ := hff
    · rw [hψ, hψ, ← hrev e, revN_of_not_adj G x he]
    · rw [hψ, hψ, ← hrev e, revN_of_not_adj G x he]
  have hreach : ∀ f f', (regionGraph G x rho).Reachable f f' → ψ f = ψ f' := by
    intro f f' ⟨w⟩
    induction w with
    | nil => rfl
    | cons hab _ ih => exact (hadj _ _ hab).trans ih
  rw [← hψ d, ← hψ d']
  exact hreach _ _ (SimpleGraph.ConnectedComponent.exact h)

theorem tauPerm_of_not_adj {d : (hullGraph x).Dart} (h : ¬ G.Adj d.fst d.snd) :
    tauPerm G x rho d = rho.rot.symm d := by
  rw [tauPerm_apply, revN_of_not_adj G x h, RotSys.face]
  simp

/-! ## Counts attached to regions -/

variable (hexp : ∀ a b, G.Adj a b → ExposedPair x a b)

theorem tauPerm_hdart (g : G.Dart) :
    tauPerm G x rho (hdart x hexp g) = rho.rot.symm (hdart x hexp g.symm) := by
  rw [tauPerm_apply, revN_of_adj G x g.adj, RotSys.face]
  rfl

/-- Hull darts off `G` in a region. -/
noncomputable def nonGCount (C : (regionGraph G x rho).ConnectedComponent) : ℕ :=
  (Finset.univ.filter fun d : (hullGraph x).Dart =>
    ¬ G.Adj d.fst d.snd ∧ region G x rho d = C).card

/-- Darts of `G` in a region. -/
noncomputable def gCount (C : (regionGraph G x rho).ConnectedComponent) : ℕ :=
  (Finset.univ.filter fun e : G.Dart => region G x rho (hdart x hexp e) = C).card

/-- Facets in a region. -/
noncomputable def facetCount (C : (regionGraph G x rho).ConnectedComponent) : ℕ :=
  (Finset.univ.filter fun f : PermutationOrbit rho.face =>
    (regionGraph G x rho).connectedComponentMk f = C).card

theorem card_region_darts (C : (regionGraph G x rho).ConnectedComponent) :
    (Finset.univ.filter fun d : (hullGraph x).Dart => region G x rho d = C).card =
      nonGCount G x rho C + gCount G x rho hexp C := by
  rw [← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun d : (hullGraph x).Dart => region G x rho d = C)
    (fun d : (hullGraph x).Dart => G.Adj d.fst d.snd), add_comm, Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  · rw [nonGCount]
    congr 1
    exact Finset.filter_congr fun d _ => and_comm
  · rw [gCount]
    symm
    refine Finset.card_bij (fun e _ => hdart x hexp e) (fun e he => ?_)
      (fun e _ e' _ h => hdart_injective x hexp h) (fun d hd => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact ⟨he, e.adj⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      refine ⟨gdart x d hd.2, ?_, hdart_gdart x hexp d hd.2⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hdart_gdart]
      exact hd.1

theorem even_nonGCount (C : (regionGraph G x rho).ConnectedComponent) :
    Even (nonGCount G x rho C) := by
  refine even_card_of_involution _ SimpleGraph.Dart.symm (fun d hd => ?_) (fun d _ => d.symm_symm)
    (fun d _ => d.symm_ne)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
  refine ⟨fun h => hd.1 h.symm, ?_⟩
  rw [region_symm G x rho hd.1, hd.2]

omit [DecidableEq V] in
include hexp in
/-- The hull darts that are darts of `G`. -/
theorem card_filter_adj :
    (Finset.univ.filter fun d : (hullGraph x).Dart => G.Adj d.fst d.snd).card =
      2 * G.edgeFinset.card := by
  rw [← SimpleGraph.dart_card_eq_twice_card_edges, ← Finset.card_univ (α := G.Dart)]
  symm
  refine Finset.card_bij (fun e _ => hdart x hexp e) (fun e _ => ?_)
    (fun e _ e' _ h => hdart_injective x hexp h) (fun d hd => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact e.adj
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact ⟨gdart x d hd, Finset.mem_univ _, hdart_gdart x hexp d hd⟩

include hexp in
theorem sum_nonGCount :
    ∑ C, nonGCount G x rho C + 2 * G.edgeFinset.card = 2 * (hullGraph x).edgeFinset.card := by
  have h1 : ∑ C, nonGCount G x rho C =
      (Finset.univ.filter fun d : (hullGraph x).Dart => ¬ G.Adj d.fst d.snd).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := region G x rho) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [nonGCount, Finset.filter_filter]
  have h3 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (hullGraph x).Dart))
    (fun d : (hullGraph x).Dart => G.Adj d.fst d.snd)
  rw [Finset.card_univ, SimpleGraph.dart_card_eq_twice_card_edges, card_filter_adj G x hexp] at h3
  rw [h1]
  omega

theorem sum_facetCount : ∑ C, facetCount G x rho C = rho.faceCount := by
  rw [rho.faceCount_eq_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := (regionGraph G x rho).connectedComponentMk)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rfl

include hexp in
theorem card_orbits_revN :
    Fintype.card (PermutationOrbit (revN G x)) =
      (hullGraph x).edgeFinset.card + G.edgeFinset.card := by
  have hinv : Function.Involutive (revN G x) := by
    intro d
    by_cases h : G.Adj d.fst d.snd
    · rw [revN_of_adj G x h, revN_of_adj G x h]
    · have h' : ¬ G.Adj d.symm.fst d.symm.snd := fun h'' => h h''.symm
      rw [revN_of_not_adj G x h, revN_of_not_adj G x h', SimpleGraph.Dart.symm_symm]
  have h := two_mul_card_orbits_involutive (revN G x) hinv
  have hfix : (Finset.univ.filter fun d => revN G x d = d) =
      Finset.univ.filter fun d : (hullGraph x).Dart => G.Adj d.fst d.snd := by
    refine Finset.filter_congr fun d _ => ⟨fun hd => ?_, fun hd => revN_of_adj G x hd⟩
    by_contra hn
    rw [revN_of_not_adj G x hn] at hd
    exact d.symm_ne hd
  rw [hfix, card_filter_adj G x hexp, SimpleGraph.dart_card_eq_twice_card_edges] at h
  omega

/-- The genus bound with one invariant per region. -/
theorem euler_bound_regions :
    Fintype.card (PermutationOrbit (revN G x)) + Fintype.card (PermutationOrbit rho.face) +
        Fintype.card (PermutationOrbit (tauPerm G x rho)) ≤
      Fintype.card (hullGraph x).Dart +
        2 * Fintype.card (regionGraph G x rho).ConnectedComponent :=
  permutation_cycle_bound_classes (revN G x) rho.face (region G x rho)
    (fun φ hrev hface d d' h => region_const G x rho φ hrev hface d d' h)

/-- The region of a face of `G`. -/
noncomputable def faceRegion (R : RotSys G) :
    PermutationOrbit R.face → (regionGraph G x rho).ConnectedComponent :=
  fun q => region G x rho (hdart x hexp q.out)

/-- The tails along a face of `G` are joined in `G`. -/
theorem reachable_of_sameCycle_face (R : RotSys G) (g g' : G.Dart) (h : R.face.SameCycle g g') :
    G.Reachable g.fst g'.fst := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, R.fst_face]
    exact ih.trans ((R.face ^ n) g).adj.reachable

/-! ## Faces of `G` inside the regions -/

variable (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
  (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (hrho : IsAngular rho x) (R : RotSys G)
  (hR : IsAngular R x)
  (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
    ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
  (hne : ∀ v, ∃ w, G.Adj v w)

include hexp hx hinj hB hrho hR hcorner hne

omit hne in
/-- From a dart of `G`, `tauPerm` reaches the next dart of its face after `k ≥ 1` steps, through
hull darts off `G`. -/
theorem tau_block (g : G.Dart) :
    ∃ k, 0 < k ∧ (tauPerm G x rho ^ k) (hdart x hexp g) = hdart x hexp (R.face g) ∧
      ∀ j, 0 < j → j < k → ¬ G.Adj ((tauPerm G x rho ^ j) (hdart x hexp g)).fst
        ((tauPerm G x rho ^ j) (hdart x hexp g)).snd := by
  obtain ⟨k, hk0, hk, hnot, -⟩ := block x hx hinj hB rho hrho hexp R hR hcorner (R.face g)
  rw [R.rot_face_eq_symm] at hk
  set d0 := hdart x hexp (R.face g) with hd0
  have hstep : ∀ m (d : (hullGraph x).Dart),
      rho.rot.symm ((rho.rot ^ (m + 1)) d) = (rho.rot ^ m) d := by
    intro m d
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  have hoff : ∀ i, 0 < i → i < k → ¬ G.Adj ((rho.rot ^ i) d0).fst ((rho.rot ^ i) d0).snd := by
    intro i hi hik
    rw [rot_pow_fst]
    exact hnot i hi hik
  have hD : ∀ j, 1 ≤ j → j ≤ k →
      (tauPerm G x rho ^ j) (hdart x hexp g) = (rho.rot ^ (k - j)) d0 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      have e : (rho.rot ^ k) d0 = (rho.rot ^ (k - 1 + 1)) d0 := by
        rw [Nat.sub_add_cancel (show 1 ≤ k by omega)]
      rw [pow_one, tauPerm_hdart, ← hk, e, hstep]
    | succ j hj ih =>
      intro hjk
      have e : k - j = k - (j + 1) + 1 := by omega
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega),
        tauPerm_of_not_adj G x rho (hoff _ (by omega) (by omega)), e, hstep]
  refine ⟨k, hk0, ?_, fun j hj hjk => ?_⟩
  · rw [hD k hk0 le_rfl, Nat.sub_self, pow_zero, Equiv.Perm.one_apply]
  · rw [hD j hj hjk.le]
    exact hoff _ (by omega) (by omega)

omit hne in
/-- G1: a face of `G` stays in one region. -/
theorem region_face_G (g : G.Dart) :
    region G x rho (hdart x hexp (R.face g)) = region G x rho (hdart x hexp g) := by
  obtain ⟨k, -, hk, -⟩ := tau_block G x rho hexp hx hinj hB hrho R hR hcorner g
  rw [← hk, region_tau_pow]

omit hne in
/-- Two darts of `G` joined by `tauPerm` lie on one face of `G`. -/
theorem sameCycle_of_tau_pow (g g' : G.Dart) (n : ℕ)
    (h : (tauPerm G x rho ^ n) (hdart x hexp g) = hdart x hexp g') : R.face.SameCycle g g' := by
  induction n using Nat.strong_induction_on generalizing g with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, Equiv.Perm.one_apply] at h
      obtain rfl := hdart_injective x hexp h
      exact Equiv.Perm.SameCycle.refl _ _
    · obtain ⟨k, hk0, hk, hoff⟩ := tau_block G x rho hexp hx hinj hB hrho R hR hcorner g
      have hkn : k ≤ n := by
        by_contra hlt
        exact hoff n hn (by omega) (by rw [h]; exact g'.adj)
      have h' : (tauPerm G x rho ^ (n - k)) (hdart x hexp (R.face g)) = hdart x hexp g' := by
        rw [← hk, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hkn, h]
      exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)).trans
        (ih (n - k) (by omega) (R.face g) h')

omit hx hinj hB hrho hR hcorner in
/-- G11: back along the hull rotation from a hull dart, the last dart of `G` before it, in the
same region, with only hull darts off `G` strictly between. -/
theorem exists_G_before (d : (hullGraph x).Dart) :
    ∃ (e : G.Dart) (j : ℕ), (rho.rot ^ j) (hdart x hexp e) = d ∧
      (∀ i, 0 < i → i ≤ j → ¬ G.Adj ((rho.rot ^ i) (hdart x hexp e)).fst
        ((rho.rot ^ i) (hdart x hexp e)).snd) ∧
      region G x rho (hdart x hexp e) = region G x rho d := by
  obtain ⟨w, hw⟩ := hne d.fst
  let f : (hullGraph x).Dart := ⟨(d.fst, w), hexp _ _ hw⟩
  have hex : ∃ j, G.Adj ((rho.rot.symm ^ j) d).fst ((rho.rot.symm ^ j) d).snd := by
    have hc : Equiv.Perm.SameCycle rho.rot.symm d f := by
      rw [← Equiv.Perm.inv_def, Equiv.Perm.sameCycle_inv]
      exact rho.rot_cycle d f rfl
    obtain ⟨j, hj⟩ := hc.exists_nat_pow_eq
    exact ⟨j, by rw [hj]; exact hw⟩
  have hjG := Nat.find_spec hex
  have hcancel : ∀ i m (y : (hullGraph x).Dart),
      (rho.rot ^ i) ((rho.rot.symm ^ (i + m)) y) = (rho.rot.symm ^ m) y := by
    intro i m y
    rw [← Equiv.Perm.inv_def, pow_add, Equiv.Perm.mul_apply, inv_pow, Equiv.Perm.inv_def,
      Equiv.apply_symm_apply]
  have hreg : ∀ i, i ≤ Nat.find hex →
      region G x rho ((rho.rot.symm ^ i) d) = region G x rho d := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hnG := Nat.find_min hex (show i < Nat.find hex by omega)
      rw [pow_succ', Equiv.Perm.mul_apply, ← tauPerm_of_not_adj G x rho hnG, region_tau,
        ih (by omega)]
  refine ⟨gdart x ((rho.rot.symm ^ Nat.find hex) d) hjG, Nat.find hex, ?_,
    fun i hi hij => ?_, ?_⟩
  · rw [hdart_gdart]
    have h := hcancel (Nat.find hex) 0 d
    rwa [add_zero, pow_zero, Equiv.Perm.one_apply] at h
  · rw [hdart_gdart]
    have h := hcancel i (Nat.find hex - i) d
    rw [Nat.add_sub_cancel' hij] at h
    rw [h]
    exact Nat.find_min hex (show Nat.find hex - i < Nat.find hex by omega)
  · rw [hdart_gdart]
    exact hreg _ le_rfl

omit hx hinj hB hrho hR hcorner in
/-- G11: every hull dart shares its region with a dart of `G` at its tail. -/
theorem exists_G_same_region (d : (hullGraph x).Dart) :
    ∃ g : G.Dart, g.fst = d.fst ∧ region G x rho (hdart x hexp g) = region G x rho d := by
  obtain ⟨e, j, hj, -, hreg⟩ := exists_G_before G x rho hexp hne d
  refine ⟨e, ?_, hreg⟩
  have h := rot_pow_fst rho (hdart x hexp e) j
  rw [hj] at h
  exact h.symm

/-- The hull corners of a region are covered by the corners of its darts of `G` (G2). -/
theorem sum_rcorner_region_le (C : (regionGraph G x rho).ConnectedComponent) :
    ∑ d ∈ Finset.univ.filter (fun d : (hullGraph x).Dart => region G x rho d = C),
        rcorner x rho d ≤
      ∑ e ∈ Finset.univ.filter (fun e : G.Dart => region G x rho (hdart x hexp e) = C),
        ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) := by
  choose k hk0 hkG hoff hsum using fun e : G.Dart =>
    block x hx hinj hB rho hrho hexp R hR hcorner e
  have hnn : ∀ d, 0 ≤ rcorner x rho d := fun d => by
    unfold rcorner ocorner
    exact (toIcoMod_mem_Ico _ _ _).1
  have hrhs : ∑ e ∈ Finset.univ.filter (fun e : G.Dart => region G x rho (hdart x hexp e) = C),
        ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) =
      ∑ p ∈ (Finset.univ.filter (fun e : G.Dart => region G x rho (hdart x hexp e) = C)).sigma
        (fun e => Finset.range (k e)), rcorner x rho ((rho.rot ^ p.2) (hdart x hexp p.1)) := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun e _ => hsum e
  rw [hrhs]
  refine le_trans ?_ (Finset.sum_image_le_of_nonneg fun u _ => hnn u)
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun u _ _ => hnn u)
  rw [Finset.mem_filter] at hd
  obtain ⟨e, j, hj, hjoff, hreg⟩ := exists_G_before G x rho hexp hne d
  have hjk : j < k e := by
    by_contra hle
    have h := hjoff (k e) (hk0 e) (by omega)
    rw [hkG e] at h
    exact h (R.rot e).adj
  rw [Finset.mem_image]
  refine ⟨⟨e, j⟩, Finset.mem_sigma.mpr ⟨?_, Finset.mem_range.mpr hjk⟩, hj⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreg.trans hd.2⟩

omit hexp hR hcorner hne in
/-- D5 summed over the facets of a region. -/
theorem sum_excess_region (C : (regionGraph G x rho).ConnectedComponent) :
    (((Finset.univ.filter fun d : (hullGraph x).Dart => region G x rho d = C).card : ℝ) -
        2 * facetCount G x rho C) * π <
      ∑ d ∈ Finset.univ.filter (fun d : (hullGraph x).Dart => region G x rho d = C),
        rcorner x rho d := by
  have hcls : ∀ q (i : Fin ((orbitPermutationCycle rho.face q).size + 1)),
      region G x rho ((orbitPermutationCycle rho.face q).point i) =
        (regionGraph G x rho).connectedComponentMk q := by
    intro q i
    show (regionGraph G x rho).connectedComponentMk (facetOf x rho _) = _
    rw [facetOf, orbitPermutationCycle_class]
  have hsum : ∀ φ : (hullGraph x).Dart → ℝ,
      ∑ d ∈ Finset.univ.filter (fun d : (hullGraph x).Dart => region G x rho d = C), φ d =
        ∑ q ∈ Finset.univ.filter (fun q : PermutationOrbit rho.face =>
          (regionGraph G x rho).connectedComponentMk q = C),
          ∑ i, φ ((orbitPermutationCycle rho.face q).point i) := by
    intro φ
    rw [Finset.sum_filter, Finset.sum_filter, ← sum_over_permutation_cycles rho.face]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : (regionGraph G x rho).connectedComponentMk q = C
    · simp [hcls, hq]
    · simp [hcls, hq]
  have hF : (Finset.univ.filter fun q : PermutationOrbit rho.face =>
      (regionGraph G x rho).connectedComponentMk q = C).Nonempty := by
    obtain ⟨f, rfl⟩ := Quot.exists_rep C
    exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hlt := Finset.sum_lt_sum_of_nonempty hF fun q _ =>
    facet_excess x hx hinj hB rho hrho (orbitPermutationCycle rho.face q)
  rw [hsum (rcorner x rho), Finset.card_eq_sum_ones, Nat.cast_sum, hsum, facetCount,
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine lt_of_eq_of_lt (Finset.sum_congr rfl fun q _ => ?_) hlt
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- G6: the excess count of a region. -/
theorem region_excess (C : (regionGraph G x rho).ConnectedComponent) :
    ((nonGCount G x rho C : ℝ) + gCount G x rho hexp C - 2 * facetCount G x rho C) * π <
      ∑ e ∈ Finset.univ.filter (fun e : G.Dart => region G x rho (hdart x hexp e) = C),
        ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) := by
  have h1 := sum_excess_region G x rho hx hinj hB hrho C
  have h2 := sum_rcorner_region_le G x rho hexp hx hinj hB hrho R hR hcorner hne C
  rw [card_region_darts G x rho hexp C] at h1
  push_cast at h1
  linarith

/-- G6 with G7: every region has `F - E_int ≥ 1`. -/
theorem region_chi (C : (regionGraph G x rho).ConnectedComponent) :
    nonGCount G x rho C + 2 ≤ 2 * facetCount G x rho C := by
  have h := region_excess G x rho hexp hx hinj hB hrho R hR hcorner hne C
  have hle : ∑ e ∈ Finset.univ.filter (fun e : G.Dart => region G x rho (hdart x hexp e) = C),
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ≤ gCount G x rho hexp C * π := by
    rw [gCount, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun e _ => (hcorner e).2.le
  have hlt : (nonGCount G x rho C : ℝ) < 2 * facetCount G x rho C := by
    have := Real.pi_pos
    nlinarith
  have hlt' : nonGCount G x rho C < 2 * facetCount G x rho C := by exact_mod_cast hlt
  obtain ⟨k, hk⟩ := even_nonGCount G x rho C
  omega

omit hne in
theorem card_G_orbits_le :
    Fintype.card (PermutationOrbit R.face) ≤ Fintype.card (PermutationOrbit (tauPerm G x rho)) := by
  refine Fintype.card_le_of_injective
    (fun q => Quotient.mk (permutationOrbitSetoid (tauPerm G x rho)) (hdart x hexp q.out)) ?_
  intro a b hab
  have hab' : Quotient.mk (permutationOrbitSetoid (tauPerm G x rho)) (hdart x hexp a.out) =
      Quotient.mk (permutationOrbitSetoid (tauPerm G x rho)) (hdart x hexp b.out) := hab
  have hs : (tauPerm G x rho).SameCycle (hdart x hexp a.out) (hdart x hexp b.out) :=
    Quotient.exact hab'
  obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
  have h := sameCycle_of_tau_pow G x rho hexp hx hinj hB hrho R hR hcorner _ _ n hn
  exact (Quotient.out_eq a).symm.trans ((Quotient.sound h).trans (Quotient.out_eq b))

omit hne in
theorem faceRegion_mk (g : G.Dart) :
    faceRegion G x rho hexp R (Quotient.mk (permutationOrbitSetoid R.face) g) =
      region G x rho (hdart x hexp g) := by
  have hpow : ∀ (n : ℕ) (e : G.Dart),
      region G x rho (hdart x hexp ((R.face ^ n) e)) = region G x rho (hdart x hexp e) := by
    intro n
    induction n with
    | zero => intro e; rfl
    | succ n ih =>
      intro e
      rw [pow_succ', Equiv.Perm.mul_apply,
        region_face_G G x rho hexp hx hinj hB hrho R hR hcorner, ih]
  have hs : R.face.SameCycle (Quotient.mk (permutationOrbitSetoid R.face) g).out g :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (permutationOrbitSetoid R.face) g))
  obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
  show region G x rho (hdart x hexp (Quotient.mk (permutationOrbitSetoid R.face) g).out) = _
  exact (hpow n _).symm.trans (congrArg (fun e => region G x rho (hdart x hexp e)) hn)

theorem faceRegion_surjective :
    Function.Surjective (faceRegion G x rho hexp R) := by
  intro C
  obtain ⟨f, rfl⟩ := Quot.exists_rep C
  obtain ⟨d, rfl⟩ := Quot.exists_rep f
  obtain ⟨g, -, hg⟩ := exists_G_same_region G x rho hexp hne d
  refine ⟨Quotient.mk _ g, ?_⟩
  rw [faceRegion_mk G x rho hexp hx hinj hB hrho R hR hcorner, hg]
  rfl

/-- The count: as many faces of `G` as regions, and `F_G = F_H - E_H + E_G`. -/
theorem regions_count :
    Fintype.card (PermutationOrbit R.face) = Fintype.card (regionGraph G x rho).ConnectedComponent ∧
      (Fintype.card (PermutationOrbit R.face) : ℤ) =
        rho.faceCount - (hullGraph x).edgeFinset.card + G.edgeFinset.card := by
  have h1 := euler_bound_regions G x rho
  have h2 := card_G_orbits_le G x rho hexp hx hinj hB hrho R hR hcorner
  have h3 := Fintype.card_le_of_surjective _
    (faceRegion_surjective G x rho hexp hx hinj hB hrho R hR hcorner hne)
  have h4 := Finset.sum_le_sum fun C (_ : C ∈ Finset.univ) =>
    region_chi G x rho hexp hx hinj hB hrho R hR hcorner hne C
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_facetCount, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at h4
  have h5 := sum_nonGCount G x rho hexp
  have h6 := card_orbits_revN G x hexp
  rw [h6, ← rho.faceCount_eq_card, SimpleGraph.dart_card_eq_twice_card_edges] at h1
  constructor <;> omega

/-- G12: Euler's relation for `G`. -/
theorem spherical_of_regions [Nonempty V] : R.Spherical := by
  obtain ⟨-, h⟩ := regions_count G x rho hexp hx hinj hB hrho R hR hcorner hne
  have hH := hull_euler x hx hinj hB rho hrho
  rw [RotSys.Spherical, R.faceCount_eq_card]
  omega

theorem faceRegion_injective :
    Function.Injective (faceRegion G x rho hexp R) := by
  obtain ⟨hcard, -⟩ := regions_count G x rho hexp hx hinj hB hrho R hR hcorner hne
  exact ((Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨faceRegion_surjective G x rho hexp hx hinj hB hrho R hR hcorner hne, hcard⟩).1

/-- One face of `G` per region. -/
theorem sameCycle_of_region (g g' : G.Dart)
    (h : region G x rho (hdart x hexp g) = region G x rho (hdart x hexp g')) :
    R.face.SameCycle g g' := by
  have hm := faceRegion_mk G x rho hexp hx hinj hB hrho R hR hcorner
  have : (Quotient.mk (permutationOrbitSetoid R.face) g : PermutationOrbit R.face) =
      Quotient.mk (permutationOrbitSetoid R.face) g' :=
    faceRegion_injective G x rho hexp hx hinj hB hrho R hR hcorner hne (by rw [hm, hm, h])
  exact Quotient.exact this

/-- G9: `G` is connected. -/
theorem connected_of_regions [Nonempty V] : G.Connected := by
  have hH := hull_connected x hx hinj hB
  have hadj : ∀ a b, (hullGraph x).Adj a b → G.Reachable a b := by
    intro a b hab
    by_cases hG : G.Adj a b
    · exact hG.reachable
    · let d : (hullGraph x).Dart := ⟨(a, b), hab⟩
      obtain ⟨ga, hga, hra⟩ := exists_G_same_region G x rho hexp hne d
      obtain ⟨gb, hgb, hrb⟩ :=
        exists_G_same_region G x rho hexp hne d.symm
      rw [region_symm G x rho hG] at hrb
      have hs := sameCycle_of_region G x rho hexp hx hinj hB hrho R hR hcorner hne ga gb
        (hra.trans hrb.symm)
      have hr := reachable_of_sameCycle_face G R ga gb hs
      rw [hga, hgb] at hr
      exact hr
  refine ⟨fun a b => ?_⟩
  obtain ⟨w⟩ := hH.preconnected a b
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab _ ih => exact (hadj _ _ hab).trans ih

/-- Every region has `F - E_int = 1`. -/
theorem region_nonG_eq (C : (regionGraph G x rho).ConnectedComponent) :
    nonGCount G x rho C + 2 = 2 * facetCount G x rho C := by
  obtain ⟨hcard, h⟩ := regions_count G x rho hexp hx hinj hB hrho R hR hcorner hne
  have h5 := sum_nonGCount G x rho hexp
  have h6 := sum_facetCount G x rho
  have hle := fun C (_ : C ∈ Finset.univ) =>
    region_chi G x rho hexp hx hinj hB hrho R hR hcorner hne C
  have hsum : ∑ C, (nonGCount G x rho C + 2) = ∑ C, 2 * facetCount G x rho C := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h6, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
    omega
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum C (Finset.mem_univ _)

/-- H1: the turning of the face of `g` is below `2π`. -/
theorem region_turn (g : G.Dart) :
    ∑ e ∈ Finset.univ.filter
        (fun e : G.Dart => region G x rho (hdart x hexp e) = region G x rho (hdart x hexp g)),
      (π - ocorner (x e.fst) (x e.snd) (x (R.rot e).snd)) < 2 * π := by
  set C := region G x rho (hdart x hexp g)
  have h := region_excess G x rho hexp hx hinj hB hrho R hR hcorner hne C
  have heq := region_nonG_eq G x rho hexp hx hinj hB hrho R hR hcorner hne C
  have heqR : (nonGCount G x rho C : ℝ) + 2 = 2 * facetCount G x rho C := by exact_mod_cast heq
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  change (gCount G x rho hexp C : ℝ) * π - _ < _
  nlinarith [Real.pi_pos]

end Regions

end Tammes15
