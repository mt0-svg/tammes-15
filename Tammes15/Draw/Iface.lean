import Tammes15.Draw.Exist
import Tammes15.FaceChain.Contact
import Tammes15.TwoConn.Contact
import Tammes15.Geom.Hexagons

/-!
# Interfaces of the drawing layer to the face modules

Statements that Theorem 4.1 takes from other parts, each proved there. All three are closed by
the theorems of those parts, with the same statements: `twoconn_contact_proof` of
`Tammes15.TwoConn.Contact`, `FaceChain.faceconvex_contact` of `Tammes15.FaceChain.Contact`, and
`Geom.rattlers_in_hexagons_proof` of `Tammes15.Geom.Hexagons`.
Their exact form is what `structure_theorem` consumes, and every hypothesis is available at that
point of the proof.

* `twoconn_contact` (TwoConn): Corollary A.6 for a contact graph, the theorem
  `twoconn` of TwoConn/Main.lean composed with `contact_exposed`.
* `faceconvex_contact` (FaceChain): Lemma A.7 in cone form, face sizes 3 to 6
  (Lemma 4.3) and 3-connectivity (Lemma 4.4).
* `rattlers_in_hexagons` (Geom): item (4) of Theorem 4.1 in the form of the fields
  `hexOf`, `hexOf_six`, `hexOf_inside`, `hexOf_distinct` of `Structured` (Propositions 4.5 and
  4.6).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Corollary A.6 for a contact graph (proved in TwoConn). -/
theorem twoconn_contact [Nonempty V] [DecidableRel G.Adj] (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (c : ℝ) (hc : c < 1) (hsep : ∀ a b, a ≠ b → ⟪x a, x b⟫ ≤ c)
    (hG : ∀ a b, G.Adj a b → ⟪x a, x b⟫ = c) (hne : ∀ v, ∃ w, G.Adj v w)
    (R : RotSys G) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π) :
    G.Connected ∧ KConnected G 2 ∧ R.Spherical ∧
      (∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e) ∧
      ∀ e : G.Dart, ∀ m n : ℕ, m < n → n < Function.minimalPeriod R.face e →
        ((R.face ^ m) e).fst ≠ ((R.face ^ n) e).fst :=
  twoconn_contact_proof x hx c hc hsep hG hne R hR hcorner

/-- Lemmas A.7 (cone form), 4.3 (sizes) and 4.4 (proved in FaceChain). -/
theorem faceconvex_contact [DecidableRel G.Adj] (dlo d : ℝ) (h7 : 7 * dlo > 2 * π)
    (hlo : dlo ≤ d) (hd : 0 < d ∧ d < π / 2) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hsep : ∀ a b, a ≠ b → d ≤ sdist (x a) (x b))
    (hG : ∀ a b, G.Adj a b ↔ a ≠ b ∧ sdist (x a) (x b) = d)
    (R : RotSys G) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, alpha d ≤ ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (hdeg : ∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5)
    (hconn : G.Connected) (h2 : KConnected G 2) (hsph : R.Spherical)
    (hface3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e)
    (hwalk : ∀ e : G.Dart, ∀ m n : ℕ, m < n → n < Function.minimalPeriod R.face e →
      ((R.face ^ m) e).fst ≠ ((R.face ^ n) e).fst) :
    StrictSupportFace R x ∧ FaceSizes R 3 6 ∧ KConnected G 3 :=
  FaceChain.faceconvex_contact dlo d h7 hlo hd x hx hsep hG R hR hcorner hdeg hconn h2 hsph
    hface3 hwalk

/-- Item (4) of Theorem 4.1: each rattler strictly inside a hexagonal face, distinct rattlers in
distinct faces (proved in Geom as `Geom.rattlers_in_hexagons_proof` with the same
statement). The conjuncts `Tammes15.dlo ≤ dlo` and `dhi ≤ Tammes15.dhi` of `hmarg` keep `d` in
the paper's range: the margins of the hexagon argument (`nor`, the one hexagon margin) hold only on
`[Tammes15.dlo, Tammes15.dhi]`, and without them the parameters bound `d` only through `hd`. -/
theorem rattlers_in_hexagons [DecidableRel G.Adj] (dlo dhi d : ℝ)
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
  Geom.rattlers_in_hexagons_proof dlo dhi d hmarg hlo hhi hd hmax X hmin emb hG hrat R hR
    hcorner hdeg h3 hsph hfaces hconv

end Tammes15
