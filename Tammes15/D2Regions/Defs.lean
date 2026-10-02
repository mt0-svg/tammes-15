import Tammes15.Hyps.Case

/-!
# D2 read on a drawing: the definitions (Definition 7.1 of the paper)

The definitions of the D2 statement read on a drawing, in the terms of the guide of plantri
(code/impl1/enum/plantri-guide.txt; Definition 7.1 and the proof of Proposition 7.5 of the
paper). They sit in their own module, above the lemmas that
prove the two theorems of `Tammes15.D2Regions.Statement`, and import only `Tammes15.Hyps.Case`, so
that `Tammes15.Hyps.Computations` can state D2 with them.

* `PlaneClass G R`: the input class of `plantri -p -f6` read on a drawing: a drawing on the sphere
  without crossings (`IsArcDrawing`), the clockwise orders seen from outside given by `R`
  (`IsAngular`: `R.rot` is the counterclockwise successor, so the clockwise order is `R.rot⁻¹`;
  `RotSys.IsoRefl` accepts either orientation), and every region (connected component of the
  sphere minus the drawing) bounded by at most 6 edges.
* `EnumCompletePlane L`: D2 with that class as hypothesis.
* `facePolygon R x e`: the open polygon of the face orbit of `e`.
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15.D2Regions

open scoped Classical

/-- The unit sphere of `E3`. -/
abbrev sphere2 : Set E3 := Metric.sphere (0 : E3) 1

/-- The closed minor arc from `p` to `q`: the unit vectors that are nonnegative combinations of
`p` and `q`. -/
def minorArc (p q : E3) : Set E3 :=
  {z | ‖z‖ = 1 ∧ ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ z = s • p + t • q}

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The arc of a dart. -/
def dartArc (x : V → E3) (e : G.Dart) : Set E3 := minorArc (x e.fst) (x e.snd)

/-- A drawing of `G` on the sphere by minor arcs without crossings: distinct unit vectors, the
ends of an edge not antipodal, no vertex on an edge other than its ends, two distinct edges
meeting only at vertices. -/
def IsArcDrawing (G : SimpleGraph V) (x : V → E3) : Prop :=
  (∀ a, ‖x a‖ = 1) ∧ Function.Injective x ∧ (∀ e : G.Dart, x e.snd ≠ -x e.fst) ∧
    (∀ (e : G.Dart) (a : V), x a ∈ dartArc x e → a = e.fst ∨ a = e.snd) ∧
    ∀ e f : G.Dart, f ≠ e → f ≠ e.symm → ∀ z ∈ dartArc x e ∩ dartArc x f, z ∈ Set.range x

/-- The point set of the drawing: the vertices and the arcs of the edges. -/
def drawingSet (G : SimpleGraph V) (x : V → E3) : Set E3 :=
  Set.range x ∪ ⋃ e : G.Dart, dartArc x e

/-- A region (a face in the guide's sense): a connected component of the sphere minus the
drawing. -/
def IsRegion (G : SimpleGraph V) (x : V → E3) (U : Set E3) : Prop :=
  ∃ p ∈ sphere2 \ drawingSet G x, U = connectedComponentIn (sphere2 \ drawingSet G x) p

/-- The edge `ε` bounds the region `U`: its arc lies in the closure of `U`. -/
def Bounds (G : SimpleGraph V) (x : V → E3) (U : Set E3) (ε : Sym2 V) : Prop :=
  ∃ e : G.Dart, e.edge = ε ∧ dartArc x e ⊆ closure U

/-- The size of a region: the number of edges that bound it. -/
noncomputable def regionSize (G : SimpleGraph V) (x : V → E3) (U : Set E3) : ℕ :=
  (G.edgeFinset.filter (Bounds G x U)).card

/-- The input class of `plantri -p -f6` read on a drawing (3-connectivity and degrees are
abstract and stay separate hypotheses of D2). -/
def PlaneClass {n : ℕ} (G : SimpleGraph (Fin n)) (R : RotSys G) : Prop :=
  ∃ x : Fin n → E3, IsArcDrawing G x ∧ IsAngular R x ∧
    ∀ U, IsRegion G x U → regionSize G x U ≤ 6

/-- D2 with the guide's class as hypothesis. -/
def EnumCompletePlane (L : Set PlaneGraph) : Prop :=
  ∀ n : ℕ, 12 ≤ n → n ≤ 15 → ∀ (G : SimpleGraph (Fin n)) (R : RotSys G),
    KConnected G 3 → (∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5) → PlaneClass G R →
      ∃ P ∈ L, P.n = n ∧ R.IsoRefl P.R

/-- The open polygon of the face orbit of `e`: the unit vectors strictly on the left of every
dart of the orbit. -/
def facePolygon (R : RotSys G) (x : V → E3) (e : G.Dart) : Set E3 :=
  {z | ‖z‖ = 1 ∧ ∀ n : ℕ, 0 < ⟪cross (x ((R.face ^ n) e).fst) (x ((R.face ^ n) e).snd), z⟫}

end Tammes15.D2Regions
