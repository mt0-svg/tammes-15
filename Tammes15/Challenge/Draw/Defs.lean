import Tammes15.Challenge.Trigrows.Sphere
import Tammes15.Challenge.Local41.Defs

/-!
# Definitions of the drawing layer

The definitions of configurations and their drawings, in the package namespace
`Tammes15`. The ones other modules already hold are imported, with the same bodies: `E3`
(`Tammes15.Statement`), `sdist`, `tdir` (`Tammes15.Trigrows.Sphere`), `alpha`, `hrad`, `rho`, `Ssum`,
`ebase`, `bangle`, `eta`, `gam` (`Tammes15.Trigrows.Defs`), `cross`, `Lmap`, `TPerp`,
`KappaBound` (`Tammes15.Local41.Defs`). This file adds the corner `ocorner`, configurations,
contact graphs, rotation systems and their faces, `KConnected`, `IsAngular`,
`StrictSupportFace`, `FaceSizes` and `Structured`. The statement of Theorem 4.1
(`structure_theorem`) is in `Tammes15.Draw.Structure`.
-/

open Real InnerProductGeometry Matrix WithLp
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-- Oriented corner at `v` from the arc `v a` to the arc `v b`, in `[0, 2π)`, counterclockwise
seen from outside (orientation given by `v`). -/
noncomputable def ocorner (v a b : E3) : ℝ :=
  toIcoMod two_pi_pos 0
    (Complex.arg ⟨⟪tdir v a, tdir v b⟫, ⟪v, cross (tdir v a) (tdir v b)⟫⟩)

/-! ## Configurations and contact graphs -/

/-- A configuration of `N` points with minimal distance at least `d`. -/
structure Config (N : ℕ) (d : ℝ) where
  pt : Fin N → E3
  unit : ∀ i, ‖pt i‖ = 1
  sep : ∀ i j, i ≠ j → d ≤ sdist (pt i) (pt j)

/-- The contact graph at distance `d` (`fromRel` symmetrises; `sdist` is symmetric anyway). -/
def contactGraph {N : ℕ} {d : ℝ} (X : Config N d) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun i j => sdist (X.pt i) (X.pt j) = d

/-! ## Rotation systems (combinatorial maps) -/

/-- A rotation system on a finite simple graph: `rot` permutes the darts at each vertex. -/
structure RotSys {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) where
  rot : Equiv.Perm G.Dart
  rot_fst : ∀ x, (rot x).fst = x.fst
  rot_cycle : ∀ x y, x.fst = y.fst → rot.SameCycle x y

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Face permutation: reverse the dart, then rotate clockwise (`rot.symm`), so that faces lie on
the left of their walks, as `StrictSupportFace` asks (the eight-point convention, `contactFaceNext`;
as in the rest of the package). -/
def RotSys.face (R : RotSys G) : Equiv.Perm G.Dart :=
  (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive).trans R.rot.symm

/-- Number of faces (orbits of the face permutation). -/
noncomputable def RotSys.faceCount (R : RotSys G) : ℕ :=
  Nat.card (Quotient (Equiv.Perm.SameCycle.setoid R.face))

/-- Genus zero: Euler's relation `V - E + F = 2`. -/
def RotSys.Spherical (R : RotSys G) : Prop :=
  (Fintype.card V : ℤ) - G.edgeFinset.card + R.faceCount = 2

/-- Vertex `k`-connectivity in the form used by plantri: more than `k` vertices, and deleting
fewer than `k` vertices leaves a connected graph. -/
def KConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce (↑S : Set V)ᶜ).Connected

/-- The angular rotation system of a drawing: `rot` sends the dart `v → a` to the dart `v → b`
with the least positive corner. -/
def IsAngular (R : RotSys G) (x : V → E3) : Prop :=
  ∀ e, ∀ f : G.Dart, f.fst = e.fst → f ≠ e →
    ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ≤ ocorner (x e.fst) (x e.snd) (x f.snd)

/-- Strict support, the cone form of "the face is a convex polygon with all corners below π"
(the form of the eight-point proof): along each face orbit `A_0 … A_{m-1}`, every other vertex
lies strictly on the inner side of the great circle of each side. -/
def StrictSupportFace (R : RotSys G) (x : V → E3) : Prop :=
  ∀ e : G.Dart, ∀ n : ℕ, (R.face ^ n) e ≠ e → (R.face ^ n) e ≠ R.face e →
    0 < ⟪cross (x e.fst) (x e.snd), x ((R.face ^ n) e).fst⟫

/-- Face sizes: the orbit of every dart has length between 3 and 6. -/
def FaceSizes (R : RotSys G) (lo hi : ℕ) : Prop :=
  ∀ e, lo ≤ Function.minimalPeriod R.face e ∧ Function.minimalPeriod R.face e ≤ hi

/-! ## Theorem 4.1 -/

/-- Conclusion of Theorem 4.1 for a configuration `X` at `d`, with the `15 - k` non-rattlers
indexed by `V`. Item (3) is stated in the cone form `StrictSupportFace`, which is what the
realisation (Definition 2.1) consumes; no perimeter of a non-polygonal set appears. -/
structure Structured {d : ℝ} (X : Config 15 d) (k : ℕ) where
  emb : V ↪ Fin 15
  card : Fintype.card V = 15 - k
  G_eq : ∀ a b, G.Adj a b ↔ (contactGraph X).Adj (emb a) (emb b)
  rattler : ∀ i, (∀ a, emb a ≠ i) → ∀ j, j ≠ i → d < sdist (X.pt i) (X.pt j)
  R : RotSys G
  angular : IsAngular R (X.pt ∘ emb)
  corners : ∀ e : G.Dart, alpha d ≤ ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd))
      (X.pt (emb (R.rot e).snd)) ∧
    ocorner (X.pt (emb e.fst)) (X.pt (emb e.snd)) (X.pt (emb (R.rot e).snd)) < π
  degrees : ∀ a, 3 ≤ G.degree a ∧ G.degree a ≤ 5
  threeConn : KConnected G 3
  spherical : R.Spherical
  faces : FaceSizes R 3 6
  convex : StrictSupportFace R (X.pt ∘ emb)
  /-- Item (4) of Theorem 4.1: each rattler lies strictly inside a hexagonal face, and distinct
  rattlers lie in distinct faces. -/
  hexOf : {i : Fin 15 // ∀ a, emb a ≠ i} → G.Dart
  hexOf_six : ∀ r, Function.minimalPeriod R.face (hexOf r) = 6
  hexOf_inside : ∀ r, ∀ n : ℕ, 0 < ⟪cross (X.pt (emb ((R.face ^ n) (hexOf r)).fst))
      (X.pt (emb ((R.face ^ n) (hexOf r)).snd)), X.pt r.1⟫
  hexOf_distinct : ∀ r r', r ≠ r' → ¬ R.face.SameCycle (hexOf r) (hexOf r')
  k_le : k ≤ 3

end Tammes15
