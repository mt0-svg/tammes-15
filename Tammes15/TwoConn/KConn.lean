import Tammes15.TwoConn.Winding

/-!
# Two-connectivity of the graph

The last step of the proof of Corollary A.6 by the convex hull (paper, Corollary
twoconn and Lemma A.5). Two neighbours `w` and `u` of a vertex `v`, consecutive in the rotation
at `v`, are joined in `G - v` by the rest of the face walk through `v → w`, whose vertices are
pairwise distinct (`face_tails_ne`). Going round the rotation at `v`, all neighbours of `v` are
joined in `G - v`, and so is every other vertex, by a walk of `G` to `v` stopped before `v`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

section KConn

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V → E3)
  (rho : RotSys (hullGraph x)) (hexp : ∀ a b, G.Adj a b → ExposedPair x a b)
  (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
  (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (hrho : IsAngular rho x) (R : RotSys G)
  (hR : IsAngular R x)
  (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
    ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
  (hne : ∀ v, ∃ w, G.Adj v w)

omit [Fintype V] [DecidableEq V] in
theorem snd_ne_of_fst {v : V} (e : G.Dart) (he : e.fst = v) : e.snd ≠ v := by
  rw [← he]
  exact e.adj.ne.symm

include hexp hx hinj hB hrho hR hcorner hne

/-- The rest of a face walk joins the two neighbours of `v` consecutive in the rotation at `v`
without passing through `v`. -/
theorem reach_rot (v : V) (e : G.Dart) (hv : e.fst = v) (hw : e.snd ≠ v)
    (hu : (R.rot e).snd ≠ v) :
    (G.induce ({v}ᶜ : Set V)).Reachable ⟨e.snd, hw⟩ ⟨(R.rot e).snd, hu⟩ := by
  subst hv
  set P := Function.minimalPeriod R.face e
  have hP : 3 ≤ P := face_period_ge_three R x (fun e => (hcorner e).1) e
  have hne' : ∀ i, 0 < i → i < P → ((R.face ^ i) e).fst ≠ e.fst := fun i hi hiP h =>
    face_tails_ne G x rho hexp hx hinj hB hrho R hR hcorner hne e 0 i hi hiP (by
      rw [pow_zero, Equiv.Perm.one_apply]
      exact h.symm)
  have hreach : ∀ i (h1 : 1 ≤ i) (h2 : i < P),
      (G.induce ({e.fst}ᶜ : Set V)).Reachable ⟨e.snd, hw⟩
        ⟨((R.face ^ i) e).fst, hne' i (by omega) h2⟩ := by
    intro i h1
    induction i, h1 using Nat.le_induction with
    | base =>
      intro h2
      have h : ((R.face ^ 1) e).fst = e.snd := by rw [pow_one, R.fst_face]
      have heq : (⟨e.snd, hw⟩ : ({e.fst}ᶜ : Set V)) =
          ⟨((R.face ^ 1) e).fst, hne' 1 (by omega) h2⟩ := Subtype.ext h.symm
      rw [heq]
    | succ i hi ih =>
      intro h2
      refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
      rw [SimpleGraph.induce_adj]
      have h := ((R.face ^ i) e).adj
      rwa [← R.fst_face, ← Equiv.Perm.mul_apply, ← pow_succ'] at h
  have hr : R.face (R.rot e).symm = e :=
    R.rot.injective (by rw [R.rot_face_eq_symm, SimpleGraph.Dart.symm_symm])
  have hP' : (R.face ^ P) e = e := by
    rw [Equiv.Perm.coe_pow]
    exact Function.isPeriodicPt_minimalPeriod R.face e
  have hlast : (R.face ^ (P - 1)) e = (R.rot e).symm := by
    apply R.face.injective
    rw [hr, ← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (by omega), hP']
  have hu' : ((R.face ^ (P - 1)) e).fst = (R.rot e).snd := by
    rw [hlast, SimpleGraph.Dart.symm_toProd, Prod.fst_swap]
  have h := hreach (P - 1) (by omega) (by omega)
  have heq : (⟨((R.face ^ (P - 1)) e).fst, hne' (P - 1) (by omega) (by omega)⟩ :
      ({e.fst}ᶜ : Set V)) = ⟨(R.rot e).snd, hu⟩ := Subtype.ext hu'
  rwa [heq] at h

/-- The neighbours of `v` are joined in `G - v`. -/
theorem reach_nbrs (v : V) (e f : G.Dart) (he : e.fst = v) (hf : f.fst = v) :
    (G.induce ({v}ᶜ : Set V)).Reachable ⟨e.snd, snd_ne_of_fst G e he⟩
      ⟨f.snd, snd_ne_of_fst G f hf⟩ := by
  obtain ⟨n, hn⟩ := (R.rot_cycle e f (he.trans hf.symm)).exists_nat_pow_eq
  subst hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have hfst : ((R.rot ^ n) e).fst = v := by rw [rot_pow_fst, he]
    have hfst' : (R.rot ((R.rot ^ n) e)).fst = v := by rw [R.rot_fst, hfst]
    have heq : (⟨((R.rot ^ (n + 1)) e).snd, snd_ne_of_fst G _ hf⟩ : ({v}ᶜ : Set V)) =
        ⟨(R.rot ((R.rot ^ n) e)).snd, snd_ne_of_fst G _ hfst'⟩ :=
      Subtype.ext (by
        show ((R.rot ^ (n + 1)) e).snd = (R.rot ((R.rot ^ n) e)).snd
        rw [pow_succ', Equiv.Perm.mul_apply])
    rw [heq]
    exact (ih hfst).trans (reach_rot G x rho hexp hx hinj hB hrho R hR hcorner hne v _ hfst _ _)

/-- Every vertex other than `v` reaches a neighbour of `v` in `G - v`. -/
theorem reach_of_walk (v : V) (e : G.Dart) (he : e.fst = v) :
    ∀ (a b : V) (_ : G.Walk a b), b = v → (ha : a ≠ v) →
      (G.induce ({v}ᶜ : Set V)).Reachable ⟨a, ha⟩ ⟨e.snd, snd_ne_of_fst G e he⟩ := by
  intro a b p
  induction p with
  | nil => intro hb ha; exact absurd hb ha
  | @cons a c b hac p ih =>
    intro hb ha
    by_cases hc : c = v
    · have hva : G.Adj v a := hc ▸ hac.symm
      exact reach_nbrs G x rho hexp hx hinj hB hrho R hR hcorner hne v ⟨(v, a), hva⟩ e rfl he
    · exact (SimpleGraph.Adj.reachable (by rw [SimpleGraph.induce_adj]; exact hac)).trans
        (ih hb hc)

/-- `G` is 2-connected. -/
theorem kconnected_two [Nonempty V] : KConnected G 2 := by
  have hconn := connected_of_regions G x rho hexp hx hinj hB hrho R hR hcorner hne
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hdeg := three_le_degree R x hx hcorner v₀ (hne v₀)
  have hlt := G.degree_lt_card_verts v₀
  unfold KConnected
  refine ⟨by omega, fun S hS => ?_⟩
  rcases Nat.lt_or_ge S.card 1 with h0 | h1
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp (show S.card = 0 by omega)
    subst hS0
    rw [Finset.coe_empty, Set.compl_empty]
    exact (SimpleGraph.Iso.connected_iff G.induceUnivIso).mpr hconn
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
    rw [Finset.coe_singleton]
    obtain ⟨w, hvw⟩ := hne v
    set e : G.Dart := ⟨(v, w), hvw⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨e.snd, hvw.ne.symm⟩, fun ⟨a, ha⟩ => ?_⟩
    obtain ⟨p⟩ := hconn.preconnected a v
    exact (reach_of_walk G x rho hexp hx hinj hB hrho R hR hcorner hne v e rfl a v p rfl ha).symm

end KConn

end Tammes15
