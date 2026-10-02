import Tammes15.TwoConn.FanCones

/-!
# Winding numbers of the face walks

Steps H4 to H9 of the proof of Corollary twoconn by the convex hull (paper, Section 3, Corollary
twoconn and Lemma hull). About a generic axis `z`, the winding of a facet is the sum of the
windings of its fan triangles (`facet_wind`), each at most one turn, and a full turn only when `z`
lies in its open cone (`tri_le`); the open fan cones are disjoint, so all facets together wind at
most once (`facets_cone_count`). The winding of a face walk of `G` is the sum of the windings of the
facets of its region, the hull edges off `G` cancelling in pairs (`region_wind`). A face walk turns
left about the axis given by the hemisphere lemma, so it winds exactly once, and its vertices are
pairwise distinct (`face_walk_injective`).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace
open Tammes15.Vendor.EM8.SquareAntiprismVerification (PermutationCycle PermutationOrbit
  permutationOrbitSetoid orbitPermutationCycle orbitPermutationCycle_class
  sum_over_permutation_cycles canonicalPermutationCycle canonicalPermutationCycle_trace
  canonicalCycle_range_iff)

namespace Tammes15

open scoped Classical
open Fin.NatCast

/-! ## Oriented angles about an axis -/

theorem oarg_swap (z p q : E3) (h : ⟪cross z p, q⟫ ≠ 0) : oarg z q p = -oarg z p q := by
  have hw : (⟨⟪tdir z q, tdir z p⟫, ⟪z, cross (tdir z q) (tdir z p)⟫⟩ : ℂ) =
      conj (⟨⟪tdir z p, tdir z q⟫, ⟪z, cross (tdir z p) (tdir z q)⟫⟩ : ℂ) := by
    apply Complex.ext
    · simp [real_inner_comm]
    · simp [cross_swap (tdir z p) (tdir z q), inner_neg_right]
  have hne : Complex.arg (⟨⟪tdir z p, tdir z q⟫, ⟪z, cross (tdir z p) (tdir z q)⟫⟩ : ℂ) ≠ π := by
    rw [Ne, Complex.arg_eq_pi_iff]
    rintro ⟨-, him⟩
    apply h
    rw [← inner_cross_tdir]
    exact him
  unfold oarg
  rw [hw, Complex.arg_conj]
  simp only [hne, ↓reduceIte]

/-- The winding of a fan triangle. -/
noncomputable def triWind (z t₀ t₁ t₂ : E3) : ℝ := oarg z t₀ t₁ + oarg z t₁ t₂ + oarg z t₂ t₀

/-- The winding of a closed polygon is the sum of the windings of its fan triangles. -/
theorem fan_telescope (z : E3) (u : ℕ → E3) (n : ℕ) (hn : 2 ≤ n) (hclose : u (n + 1) = u 0)
    (hanti : ∀ a, 2 ≤ a → a ≤ n → oarg z (u a) (u 0) = -oarg z (u 0) (u a)) :
    ∑ k ∈ Finset.range (n + 1), oarg z (u k) (u (k + 1)) =
      ∑ a ∈ Finset.Ico 1 n, triWind z (u 0) (u a) (u (a + 1)) := by
  have aux : ∀ j, 1 ≤ j → j ≤ n →
      ∑ a ∈ Finset.Ico 1 j, triWind z (u 0) (u a) (u (a + 1)) + oarg z (u 0) (u j) =
        oarg z (u 0) (u 1) + ∑ a ∈ Finset.Ico 1 j, oarg z (u a) (u (a + 1)) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; simp
    | succ j hj ih =>
      intro hjn
      rw [Finset.sum_Ico_succ_top hj, Finset.sum_Ico_succ_top hj]
      have h1 := ih (by omega)
      have h2 := hanti (j + 1) (by omega) hjn
      have h3 : triWind z (u 0) (u j) (u (j + 1)) =
          oarg z (u 0) (u j) + oarg z (u j) (u (j + 1)) + oarg z (u (j + 1)) (u 0) := rfl
      linarith
  have h1 := aux n (by omega) le_rfl
  have h2 := hanti n
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hclose]
  have h3 := h2 hn le_rfl
  simp only [zero_add] at h1 ⊢
  linarith

/-- A fan triangle winds a full turn only about an axis in its open cone. -/
theorem tri_le (z t₀ t₁ t₂ : E3) (hz : ‖z‖ = 1) (h₁ : ⟪cross z t₀, t₁⟫ ≠ 0)
    (h₂ : ⟪cross z t₁, t₂⟫ ≠ 0) (h₃ : ⟪cross z t₂, t₀⟫ ≠ 0) :
    triWind z t₀ t₁ t₂ ≤ if InCone z t₀ t₁ t₂ then 2 * π else 0 := by
  unfold triWind InCone
  rw [triangle_oarg z t₀ t₁ t₂ hz h₁ h₂ h₃]
  split_ifs <;> linarith [pi_pos]

theorem cross_ne_zero_of_det {a b c : E3} (h : ⟪cross a b, c⟫ ≠ 0) : cross a b ≠ 0 := by
  intro h0
  rw [h0, inner_zero_left] at h
  exact h rfl

/-! ## Windings of the facets -/

section Facets

variable {V : Type} [Fintype V] [DecidableEq V]
variable (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
  (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
  (hrho : IsAngular rho x)

/-- An axis in general position: off every plane through two points of `x`. -/
def Generic (z : E3) : Prop := ∀ a b : V, cross (x a) (x b) ≠ 0 → ⟪cross z (x a), x b⟫ ≠ 0

include hx hinj hB hrho

/-- H7: the winding of a facet is the sum of the windings of its fan triangles. -/
theorem facet_wind (z : E3) (hz : Generic x z) (C : PermutationCycle rho.face) :
    ∑ i, oarg z (x (C.point i).fst) (x (C.point i).snd) =
      ∑ a ∈ Finset.Ico 1 C.size,
        triWind z (cpt x rho C 0) (cpt x rho C a) (cpt x rho C (a + 1)) := by
  have hs := cycle_size_ge_two x hx hinj hB rho hrho C
  have hF : ∀ i : Fin (C.size + 1), oarg z (x (C.point i).fst) (x (C.point i).snd) =
      oarg z (cpt x rho C i.val) (cpt x rho C (i.val + 1)) := fun i => by
    unfold cpt
    rw [← cvert_snd x rho C i.val]
    unfold cvert
    rw [Fin.cast_val_eq_self]
  rw [Finset.sum_congr rfl fun i _ => hF i,
    Fin.sum_univ_eq_sum_range (fun k => oarg z (cpt x rho C k) (cpt x rho C (k + 1)))]
  refine fan_telescope z (cpt x rho C) C.size hs ?_ ?_
  · unfold cpt
    rw [cvert_size]
  · intro a ha haS
    apply oarg_swap
    apply hz
    have h := fan_det_pos x hx hinj hB rho hrho C 1 a le_rfl (by omega) haS
    rw [← inner_cross_cyc, ← inner_cross_cyc] at h
    have h' := cross_ne_zero_of_det h.ne'
    rw [cross_swap] at h'
    exact neg_ne_zero.mp h'

/-- H8: all facets together wind at most once about a generic axis. -/
theorem facets_cone_count (z : E3) :
    ∑ f : PermutationOrbit rho.face, ∑ a ∈ Finset.Ico 1 (orbitPermutationCycle rho.face f).size,
      (if InCone z (cpt x rho (orbitPermutationCycle rho.face f) 0)
          (cpt x rho (orbitPermutationCycle rho.face f) a)
          (cpt x rho (orbitPermutationCycle rho.face f) (a + 1)) then 2 * π else 0) ≤ 2 * π := by
  rw [Finset.sum_sigma', Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  apply mul_le_of_le_one_left (by positivity)
  norm_cast
  rw [Finset.card_le_one]
  rintro ⟨f, a⟩ hfa ⟨f', b⟩ hfb
  simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_Ico] at hfa hfb
  obtain ⟨hf, hab⟩ := cone_unique x hx hinj hB rho hrho f f' a b hfa.1.1 (by omega) hfb.1.1
    (by omega) z hfa.2 hfb.2
  subst hf
  subst hab
  rfl

theorem fan_tri_le (z : E3) (hz1 : ‖z‖ = 1) (hz : Generic x z) (C : PermutationCycle rho.face)
    (a : ℕ) (ha : a ∈ Finset.Ico 1 C.size) :
    triWind z (cpt x rho C 0) (cpt x rho C a) (cpt x rho C (a + 1)) ≤
      if InCone z (cpt x rho C 0) (cpt x rho C a) (cpt x rho C (a + 1)) then 2 * π else 0 := by
  rw [Finset.mem_Ico] at ha
  have hD := (fan_step x hx hinj hB rho hrho C a ha.1 (by omega)).ne'
  refine tri_le z _ _ _ hz1 (hz _ _ (cross_ne_zero_of_det hD))
    (hz _ _ (cross_ne_zero_of_det (c := cpt x rho C 0) ?_))
    (hz _ _ (cross_ne_zero_of_det (c := cpt x rho C a) ?_))
  · rw [inner_cross_cyc]
    exact hD
  · rw [inner_cross_cyc, inner_cross_cyc]
    exact hD

end Facets

/-! ## Windings of the face walks of `G` -/

section Walks

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V → E3)
  (rho : RotSys (hullGraph x)) (hexp : ∀ a b, G.Adj a b → ExposedPair x a b)
  (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
  (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (hrho : IsAngular rho x) (R : RotSys G)
  (hR : IsAngular R x)
  (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
    ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
  (hne : ∀ v, ∃ w, G.Adj v w)

include hexp hx hinj hB hrho in
/-- H6: the facets of a region wind as the darts of `G` in it, the hull edges off `G` cancelling. -/
theorem region_wind (z : E3) (hz : Generic x z) (K : (regionGraph G x rho).ConnectedComponent) :
    ∑ f ∈ Finset.univ.filter (fun f => (regionGraph G x rho).connectedComponentMk f = K),
        ∑ i, oarg z (x ((orbitPermutationCycle rho.face f).point i).fst)
          (x ((orbitPermutationCycle rho.face f).point i).snd) =
      ∑ e ∈ Finset.univ.filter (fun e : G.Dart => region G x rho (hdart x hexp e) = K),
        oarg z (x e.fst) (x e.snd) := by
  set φ : (hullGraph x).Dart → ℝ := fun d => oarg z (x d.fst) (x d.snd)
  have e1 : ∀ f i, region G x rho ((orbitPermutationCycle rho.face f).point i) =
      (regionGraph G x rho).connectedComponentMk f := fun f i => by
    unfold region facetOf
    rw [orbitPermutationCycle_class]
  have h1 : ∑ f ∈ Finset.univ.filter (fun f => (regionGraph G x rho).connectedComponentMk f = K),
      ∑ i, φ ((orbitPermutationCycle rho.face f).point i) =
      ∑ d ∈ Finset.univ.filter (fun d => region G x rho d = K), φ d := by
    rw [Finset.sum_filter, Finset.sum_filter,
      ← sum_over_permutation_cycles rho.face (fun d => if region G x rho d = K then φ d else 0)]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with h
    · exact Finset.sum_congr rfl fun i _ => by simp only [e1, h, ↓reduceIte]
    · exact (Finset.sum_eq_zero fun i _ => by simp only [e1, h, ↓reduceIte]).symm
  change ∑ f ∈ _, ∑ i, φ _ = _
  rw [h1, ← Finset.sum_filter_add_sum_filter_not _
    (fun d : (hullGraph x).Dart => G.Adj d.fst d.snd)]
  have h2 : ∑ d ∈ (Finset.univ.filter fun d => region G x rho d = K).filter
      (fun d : (hullGraph x).Dart => ¬ G.Adj d.fst d.snd), φ d = 0 := by
    refine Finset.sum_involution (fun d _ => d.symm) (fun d hd => ?_) (fun d _ _ => d.symm_ne)
      (fun d hd => ?_) (fun d _ => d.symm_symm)
    · simp only [φ, SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap]
      show oarg z (x d.fst) (x d.snd) + oarg z (x d.snd) (x d.fst) = 0
      rw [oarg_swap z (x d.fst) (x d.snd) (hz _ _ (cross_ne_zero_of_det
        (hull_det_pos x hx hinj hB rho hrho d).ne')), add_neg_cancel]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      refine ⟨?_, fun h => hd.2 h.symm⟩
      rw [region_symm G x rho hd.2, hd.1]
  have h3 : ∑ d ∈ (Finset.univ.filter fun d => region G x rho d = K).filter
      (fun d : (hullGraph x).Dart => G.Adj d.fst d.snd), φ d =
      ∑ e ∈ Finset.univ.filter (fun e : G.Dart => region G x rho (hdart x hexp e) = K),
        oarg z (x e.fst) (x e.snd) := by
    symm
    refine Finset.sum_nbij (hdart x hexp) ?_ (hdart_injective x hexp).injOn ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact ⟨he, e.adj⟩
    · intro d hd
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hd
      refine ⟨gdart x d hd.2, ?_, hdart_gdart x hexp d hd.2⟩
      rw [Finset.mem_coe, Finset.mem_filter, hdart_gdart]
      exact ⟨Finset.mem_univ _, hd.1.2⟩
    · intro e _
      rfl
  rw [h2, add_zero, h3]

include hexp hx hinj hB hrho hR hcorner hne

omit hne in
theorem region_iterate (g : G.Dart) (n : ℕ) :
    region G x rho (hdart x hexp (R.face^[n] g)) = region G x rho (hdart x hexp g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',
      region_face_G G x rho hexp hx hinj hB hrho R hR hcorner, ih]

/-- The darts of `G` in the region of a face are the darts of the face. -/
theorem walk_sum (g : G.Dart) (φ : G.Dart → ℝ) :
    ∑ e ∈ Finset.univ.filter
        (fun e : G.Dart => region G x rho (hdart x hexp e) = region G x rho (hdart x hexp g)), φ e =
      ∑ i, φ ((canonicalPermutationCycle R.face g).point i) := by
  set W := canonicalPermutationCycle R.face g
  have hset : Finset.univ.filter
      (fun e : G.Dart => region G x rho (hdart x hexp e) = region G x rho (hdart x hexp g)) =
      Finset.univ.image W.point := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact (canonicalCycle_range_iff R.face g e).mpr
        (sameCycle_of_region G x rho hexp hx hinj hB hrho R hR hcorner hne g e h.symm)
    · rintro ⟨i, rfl⟩
      rw [canonicalPermutationCycle_trace]
      exact region_iterate G x rho hexp hx hinj hB hrho R hR hcorner g i.val
  rw [hset, Finset.sum_image fun i _ j _ h => W.injective h]

/-- H9: the vertices of a face walk of `G` are pairwise distinct over one period. -/
theorem face_walk_injective (g : G.Dart) :
    Function.Injective fun i => ((canonicalPermutationCycle R.face g).point i).fst := by
  set W := canonicalPermutationCycle R.face g with hW
  set L := W.size
  set w : Fin (L + 1) → E3 := fun i => x (W.point i).fst with hw
  have hsnd : ∀ i, (W.point i).snd = (W.point (i + 1)).fst := fun i => by
    rw [← W.step, R.fst_face]
  have hrot : ∀ i, (R.rot (W.point i)).snd = (W.point (i - 1)).fst := fun i => by
    have h := W.step (i - 1)
    rw [sub_add_cancel] at h
    rw [← h, R.rot_face_eq_symm, SimpleGraph.Dart.symm_toProd, Prod.snd_swap]
  have hcor : ∀ i, ocorner (x (W.point i).fst) (x (W.point i).snd) (x (R.rot (W.point i)).snd) =
      ocorner (w i) (w (i + 1)) (w (i - 1)) := fun i => by rw [hsnd, hrot]
  have hturn : ∀ i, 0 < ⟪cross (w i) (w (i + 1)), w (i - 1)⟫ := fun i => by
    have h := (ocorner_pos_lt_pi_iff _ _ _).mp (hcorner (W.point i))
    rw [hsnd, hrot] at h
    exact h
  have hsum : ∑ i, (π - ocorner (w i) (w (i + 1)) (w (i - 1))) < 2 * π := by
    have h := region_turn G x rho hexp hx hinj hB hrho R hR hcorner hne g
    rw [walk_sum G x rho hexp hx hinj hB hrho R hR hcorner hne g
      (fun e => π - ocorner (x e.fst) (x e.snd) (x (R.rot e).snd))] at h
    rw [← hW] at h
    simpa only [hcor] using h
  obtain ⟨z₀, hz₀⟩ := walk_axis L w (fun i => hx _) hturn hsum
  set U : Set E3 := {z | ∀ i, 0 < ⟪z, cross (w i) (w (i + 1))⟫} with hUdef
  have hU : IsOpen U := by
    have hUi : U = ⋂ i, {z | 0 < ⟪z, cross (w i) (w (i + 1))⟫} := by
      ext z
      simp [U]
    rw [hUi]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_id.inner continuous_const)
  have hz₀U : z₀ ∈ U := fun i => by
    have h := hz₀ i
    rwa [← inner_cross_cyc, real_inner_comm] at h
  set S : Finset E3 :=
    (Finset.univ.image fun p : V × V => cross (x p.1) (x p.2)).filter (· ≠ 0)
  obtain ⟨z₁, hz₁U, hz₁S⟩ := exists_generic U hU ⟨z₀, hz₀U⟩ S
    (fun m hm => (Finset.mem_filter.mp hm).2)
  have hz₁0 : z₁ ≠ 0 := by
    rintro rfl
    have h := hz₁U 0
    rw [inner_zero_left] at h
    exact lt_irrefl _ h
  have hnz : 0 < ‖z₁‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hz₁0)
  set z := ‖z₁‖⁻¹ • z₁
  have hzu : ‖z‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz₁0)]
  have hdet : ∀ p q, ⟪cross z p, q⟫ = ‖z₁‖⁻¹ * ⟪z₁, cross p q⟫ := fun p q => by
    rw [cross_smul_left, real_inner_smul_left, ← inner_cross_cyc, real_inner_comm]
  have hgen : Generic x z := fun a b hab => by
    rw [hdet]
    exact mul_ne_zero hnz.ne' (hz₁S _ (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩, hab⟩))
  have hpos : ∀ i, 0 < ⟪cross z (w i), w (i + 1)⟫ := fun i => by
    rw [hdet]
    exact mul_pos hnz (hz₁U i)
  have hle : ∑ i, oarg z (w i) (w (i + 1)) ≤ 2 * π := by
    have h1 := walk_sum G x rho hexp hx hinj hB hrho R hR hcorner hne g
      (fun e => oarg z (x e.fst) (x e.snd))
    rw [← hW] at h1
    have h2 := region_wind G x rho hexp hx hinj hB hrho z hgen (region G x rho (hdart x hexp g))
    have h3 : ∑ i, oarg z (w i) (w (i + 1)) =
        ∑ i, oarg z (x (W.point i).fst) (x (W.point i).snd) :=
      Finset.sum_congr rfl fun i _ => by rw [hsnd]
    rw [h3, ← h1, ← h2]
    calc _ = ∑ f ∈ Finset.univ.filter
            (fun f => (regionGraph G x rho).connectedComponentMk f =
              region G x rho (hdart x hexp g)),
          ∑ a ∈ Finset.Ico 1 (orbitPermutationCycle rho.face f).size,
            triWind z (cpt x rho (orbitPermutationCycle rho.face f) 0)
              (cpt x rho (orbitPermutationCycle rho.face f) a)
              (cpt x rho (orbitPermutationCycle rho.face f) (a + 1)) :=
          Finset.sum_congr rfl fun f _ => facet_wind x hx hinj hB rho hrho z hgen _
      _ ≤ ∑ f ∈ Finset.univ.filter
            (fun f => (regionGraph G x rho).connectedComponentMk f =
              region G x rho (hdart x hexp g)),
          ∑ a ∈ Finset.Ico 1 (orbitPermutationCycle rho.face f).size,
            (if InCone z (cpt x rho (orbitPermutationCycle rho.face f) 0)
              (cpt x rho (orbitPermutationCycle rho.face f) a)
              (cpt x rho (orbitPermutationCycle rho.face f) (a + 1)) then 2 * π else 0) :=
          Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun a ha =>
            fan_tri_le x hx hinj hB rho hrho z hzu hgen _ a ha
      _ ≤ ∑ f : PermutationOrbit rho.face,
          ∑ a ∈ Finset.Ico 1 (orbitPermutationCycle rho.face f).size,
            (if InCone z (cpt x rho (orbitPermutationCycle rho.face f) 0)
              (cpt x rho (orbitPermutationCycle rho.face f) a)
              (cpt x rho (orbitPermutationCycle rho.face f) (a + 1)) then 2 * π else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun f _ _ => Finset.sum_nonneg fun a _ => by split_ifs <;> positivity)
      _ ≤ 2 * π := facets_cone_count x hx hinj hB rho hrho z
  have htdir : ∀ i, tdir z (w i) ≠ 0 := fun i h => by
    have h' := hpos i
    rw [← inner_cross_tdir, h] at h'
    simp [cross] at h'
  obtain ⟨k, hk⟩ := sum_oarg_mem z hzu L w htdir
  have hgt : 0 < ∑ i, oarg z (w i) (w (i + 1)) :=
    Finset.sum_pos (fun i _ => ((oarg_mem_of_det z _ _).1 (hpos i)).1) Finset.univ_nonempty
  have hk1 : k = 1 := by
    rw [hk] at hgt hle
    have h1 : (0 : ℝ) < k := by nlinarith [pi_pos]
    have h2 : (k : ℝ) ≤ 1 := by nlinarith [pi_pos]
    have h3 : 0 < k := by exact_mod_cast h1
    have h4 : k ≤ 1 := by exact_mod_cast h2
    omega
  have h2pi : ∑ i, oarg z (w i) (w (i + 1)) = 2 * π := by
    rw [hk, hk1, Int.cast_one, mul_one]
  have hinjw := injective_of_winding_one z hzu L w hpos h2pi
  intro i j hij
  exact hinjw (congrArg x hij)

/-- The vertices of a face walk of `G` over one period are pairwise distinct. -/
theorem face_tails_ne (e : G.Dart) (m n : ℕ) (hmn : m < n)
    (hn : n < Function.minimalPeriod R.face e) : ((R.face ^ m) e).fst ≠ ((R.face ^ n) e).fst := by
  have hper : Function.IsPeriodicPt R.face ((canonicalPermutationCycle R.face e).size + 1) e := by
    have h := (canonicalPermutationCycle R.face e).step (Fin.last _)
    rw [Fin.last_add_one, canonicalPermutationCycle_trace, canonicalPermutationCycle_trace] at h
    simp only [Fin.val_last, Fin.val_zero, Function.iterate_zero, id_eq] at h
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply']
    exact h
  have hle := hper.minimalPeriod_le (Nat.succ_pos _)
  intro h
  have hinjW := face_walk_injective G x rho hexp hx hinj hB hrho R hR hcorner hne e
    (a₁ := ⟨m, by omega⟩) (a₂ := ⟨n, by omega⟩)
    (by
      simp only [canonicalPermutationCycle_trace]
      rw [← Equiv.Perm.coe_pow, ← Equiv.Perm.coe_pow]
      exact h)
  have := congrArg Fin.val hinjW
  simp only at this
  omega

end Walks

end Tammes15
