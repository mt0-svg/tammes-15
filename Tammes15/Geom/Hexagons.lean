import Tammes15.Geom.Cover
import Tammes15.Geom.Onehex
import Tammes15.Draw.Exist

/-!
# Item (4) of Theorem 3.1: each rattler strictly inside its own hexagon

`rattlers_core`: for the drawn contact graph of a configuration at `d ∈ [dlo, dhi]`, each rattler
lies strictly inside some face (`exists_face_inside`), which is a hexagon (`nor` excludes the faces
with at most five vertices), and two rattlers never share a face (`onehex`).

`rattlers_in_hexagons_proof` has the statement of `Tammes15.rattlers_in_hexagons`
(`Tammes15.Draw.Iface`). Its conjuncts `Tammes15.dlo ≤ dlo` and `dhi ≤ Tammes15.dhi` put `d` in
the interval where the margins are proved: the margin of Proposition onehex fails above
`d ≈ 58.6°` (code/lean/geom/onehex_range.gp). `KConnected G 3` gives a vertex, which
`exists_face_inside` needs.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem alpha_pos_of_mem (d : ℝ) (hd : 0 < d ∧ d < π / 2) : 0 < alpha d := by
  rcases hd with ⟨hd_left, hd_right⟩
  have hcos_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hd_right⟩
  have h_div_lt_one : cos d / (1 + cos d) < 1 := by
    have hpos : 0 < 1 + cos d := by linarith
    rw [div_lt_one hpos]
    linarith
  rw [Tammes15.alpha]
  rw [Real.arccos_pos]
  exact h_div_lt_one

/-- A point inside the face of a dart is inside the face of every dart of its orbit. -/
theorem inside_of_sameCycle (R : RotSys G) (x : V → E3) (e e' : G.Dart)
    (h : R.face.SameCycle e e') (y : E3)
    (hy : ∀ n : ℕ, 0 < ⟪cross (x ((R.face ^ n) e').fst) (x ((R.face ^ n) e').snd), y⟫) :
    ∀ n : ℕ, 0 < ⟪cross (x ((R.face ^ n) e).fst) (x ((R.face ^ n) e).snd), y⟫ := by
  classical
  intro n
  obtain ⟨k, hk⟩ := h.symm.exists_nat_pow_eq
  have h_eq : (R.face ^ n) e = (R.face ^ (n + k)) e' := by
    calc
      (R.face ^ n) e = (R.face ^ n) ((R.face ^ k) e') := by rw [hk]
      _ = ((R.face ^ n) * (R.face ^ k)) e' := by rw [← Equiv.Perm.mul_apply]
      _ = (R.face ^ (n + k)) e' := by rw [← pow_add]
  rw [h_eq]
  exact hy (n + k)

/-- Item (4) of Theorem 3.1 for `d` in the interval of the constants. -/
theorem rattlers_core [DecidableRel G.Adj] [Nonempty V] (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi)
    (hd : 0 < d ∧ d < π / 2) (X : Config 15 d) (emb : V ↪ Fin 15)
    (hG : ∀ a b, G.Adj a b ↔ (contactGraph X).Adj (emb a) (emb b))
    (hrat : ∀ i, (∀ a, emb a ≠ i) → ∀ j, j ≠ i → d < sdist (X.pt i) (X.pt j))
    (R : RotSys G) (hR : IsAngular R (X.pt ∘ emb))
    (hcorner : ∀ e : G.Dart,
      alpha d ≤ ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) ∧
        ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) < π)
    (hdeg : ∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5)
    (hfaces : FaceSizes R 3 6) (hconv : StrictSupportFace R (X.pt ∘ emb)) :
    ∃ hexOf : {i : Fin 15 // ∀ a, emb a ≠ i} → G.Dart,
      (∀ r, Function.minimalPeriod R.face (hexOf r) = 6) ∧
      (∀ r, ∀ n : ℕ, 0 < ⟪cross (X.pt (emb ((R.face ^ n) (hexOf r)).fst))
        (X.pt (emb ((R.face ^ n) (hexOf r)).snd)), X.pt r.1⟫) ∧
      ∀ r r', r ≠ r' → ¬ R.face.SameCycle (hexOf r) (hexOf r') := by
  set x : V → E3 := X.pt ∘ emb with hxdef
  have hx : ∀ v, ‖x v‖ = 1 := fun v => X.unit _
  have hGd : ∀ a b, G.Adj a b → sdist (x a) (x b) = d := fun a b h =>
    ((contactGraph_adj_iff X _ _).mp ((hG a b).mp h)).2
  have hne : ∀ v, ∃ w, G.Adj v w := fun v =>
    (G.degree_pos_iff_exists_adj v).mp (by have := (hdeg v).1; omega)
  have hapos := alpha_pos_of_mem d hd
  have hcorner' : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π := fun e =>
    ⟨lt_of_lt_of_le hapos (hcorner e).1, (hcorner e).2⟩
  have hface3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e := fun e => (hfaces e).1
  have hfar : ∀ r : {i : Fin 15 // ∀ a, emb a ≠ i}, ∀ v, d < sdist (X.pt r.1) (x v) :=
    fun r v => hrat r.1 r.2 (emb v) (r.2 v)
  choose hexOf hexIn using fun r : {i : Fin 15 // ∀ a, emb a ≠ i} =>
    exists_face_inside x hx d hd hGd hne R hR hcorner' hconv hface3 (X.pt r.1) (X.unit _) (hfar r)
  have hpoly : ∀ e, IsCPoly (Function.minimalPeriod R.face e) (faceSeq R x e) := fun e =>
    faceSeq_isCPoly R x hx hconv e (hface3 e)
  have hsidef : ∀ e i, sdist (faceSeq R x e i) (faceSeq R x e (i + 1)) = d := by
    intro e i
    obtain ⟨f, h1, h2⟩ := faceSeq_adj R x e i
    rw [h1, h2]
    exact hGd _ _ f.adj
  have hinf : ∀ r, Inside (faceSeq R x (hexOf r)) (X.pt r.1) := fun r =>
    (inside_faceSeq_iff R x _ _).mpr (hexIn r)
  have hfarf : ∀ r : {i : Fin 15 // ∀ a, emb a ≠ i}, ∀ e i, d ≤ sdist (X.pt r.1) (faceSeq R x e i) :=
    fun r e i => (hfar r _).le
  have hsix : ∀ r, Function.minimalPeriod R.face (hexOf r) = 6 := by
    intro r
    have h36 := hfaces (hexOf r)
    by_contra h6
    exact nor d hlo hhi (hpoly (hexOf r)) (by omega) (hsidef _) (X.pt r.1) (X.unit _) (hinf r)
      (hfarf r _)
  refine ⟨hexOf, hsix, hexIn, fun r r' hrr' hsc => ?_⟩
  have hin' : Inside (faceSeq R x (hexOf r)) (X.pt r'.1) :=
    (inside_faceSeq_iff R x _ _).mpr (inside_of_sameCycle R x _ _ hsc _ (hexIn r'))
  have hA6 : IsCPoly 6 (faceSeq R x (hexOf r)) := hsix r ▸ hpoly (hexOf r)
  exact onehex d hlo hhi hA6 (hsidef _) (X.pt r.1) (X.pt r'.1) (X.unit _) (X.unit _) (hinf r) hin'
    (hfarf r _) (hfarf r' _) (X.sep _ _ (fun h => hrr' (Subtype.ext h)))

set_option linter.unusedVariables false in
/-- Item (4) of Theorem 3.1, the statement of `Tammes15.rattlers_in_hexagons` (the hypotheses
`hmax`, `hmin`, `h3`, `hsph` are not needed). -/
theorem rattlers_in_hexagons_proof [DecidableRel G.Adj] (dlo dhi d : ℝ)
    (hmarg : 7 * dlo > 2 * π ∧ alpha dhi < 2 * π / 5 ∧ Tammes15.dlo ≤ dlo ∧ dhi ≤ Tammes15.dhi)
    (hlo : dlo ≤ d) (hhi : d ≤ dhi)
    (hd : 0 < d ∧ d < π / 2) (hmax : IsGreatest {d | Nonempty (Config 15 d)} d)
    (X : Config 15 d) (hmin : ∀ Y : Config 15 d, contactCount X ≤ contactCount Y)
    (emb : V ↪ Fin 15) (hG : ∀ a b, G.Adj a b ↔ (contactGraph X).Adj (emb a) (emb b))
    (hrat : ∀ i, (∀ a, emb a ≠ i) → ∀ j, j ≠ i → d < sdist (X.pt i) (X.pt j))
    (R : RotSys G) (hR : IsAngular R (X.pt ∘ emb))
    (hcorner : ∀ e : G.Dart,
      alpha d ≤ ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) ∧
        ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) < π)
    (hdeg : ∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5) (h3 : KConnected G 3) (hsph : R.Spherical)
    (hfaces : FaceSizes R 3 6) (hconv : StrictSupportFace R (X.pt ∘ emb)) :
    ∃ hexOf : {i : Fin 15 // ∀ a, emb a ≠ i} → G.Dart,
      (∀ r, Function.minimalPeriod R.face (hexOf r) = 6) ∧
      (∀ r, ∀ n : ℕ, 0 < ⟪cross (X.pt (emb ((R.face ^ n) (hexOf r)).fst))
        (X.pt (emb ((R.face ^ n) (hexOf r)).snd)), X.pt r.1⟫) ∧
      ∀ r r', r ≠ r' → ¬ R.face.SameCycle (hexOf r) (hexOf r') :=
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by have := h3.1; omega)
  rattlers_core d (le_trans hmarg.2.2.1 hlo) (le_trans hhi hmarg.2.2.2) hd X emb hG hrat R hR
    hcorner hdeg hfaces hconv

end Tammes15.Geom
