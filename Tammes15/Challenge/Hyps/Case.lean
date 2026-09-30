import Tammes15.Challenge.Draw.Defs
import Tammes15.Challenge.Glue.Enclosure
import Tammes15.Challenge.Trigrows.Margins

/-!
# Cases, assignments, the relation system, the gluing, Pair and Local

The objects of Section 5 of the paper in the form the computations check them.

* A *case* is a `PlaneGraph` (a rotation system on a simple graph with vertex set `Fin n`) and a
  `HexChoice` of `k` hexagonal faces holding the free points (rattlers); its points `Pts P k` are the
  `n` vertices and the `k` free points.
* An *assignment* `Assign P k` gives values to the variables of the test: the edge length `d`, one
  corner per dart (the corner at `e.fst` from `e` to `R.rot e`, which is the corner of the face of
  `e` at that vertex), and the six distances `r` from each free point to the corners
  `A_j = ((R.face ^ j) (base m)).fst` of its hexagon.
* `RelSys` is the conjunction of the relations that the level-2 program applies to a box (Section 5.2,
  the rows; Section 5.3, (T1) to (T8)), each as a statement about real numbers, for every face, every
  rotation of it and every free point.
* `glueY` is the configuration glued from an assignment along a spanning tree (Section 5.4):
  `F(v₀) = I`, `F(w) = F(v) R_z(φ) R_y(d) Z` with `φ` the sum of the corners at `v` from the reference
  dart of `v` to `w`, `Y(w) = F(w) e₃`; a free point is placed from a corner `A_i` of its hexagon.
* `PairFires` (two points not joined by an edge at chord distance below `2 sin (d/2)`) and
  `LocalFires` (every point within `1.04·10⁻³` of an isometric image of a frame configuration, under a
  bijection of the fifteen points) are the two tests of Section 5.4 on a configuration.
* `Realisation` is Definition 5.1, and `assignOf` reads the assignment of a realisation.
-/

open Real Matrix
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-! ## Cases -/

/-- A plane graph given by a rotation system on a simple graph with vertex set `Fin n`: an entry
of the enumeration (Computation 6.1) with its rotation system. -/
structure PlaneGraph where
  n : ℕ
  G : SimpleGraph (Fin n)
  R : RotSys G

/-- The class of Section 5.1: 3-connected, degrees 3 to 5, faces of size 3 to 6, genus zero. -/
def InClass (P : PlaneGraph) : Prop :=
  KConnected P.G 3 ∧ (∀ a, 3 ≤ P.G.degree a ∧ P.G.degree a ≤ 5) ∧ FaceSizes P.R 3 6 ∧
    P.R.Spherical

/-- The dart map of a graph isomorphism. -/
def dmap {V V' : Type} {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') (e : G.Dart) :
    G'.Dart :=
  ⟨(φ e.fst, φ e.snd), φ.map_adj_iff.mpr e.adj⟩

/-- Isomorphic rotation systems, possibly reversing the orientation: a graph isomorphism that
carries `R.rot` to `R'.rot` or to its inverse. -/
def RotSys.IsoRefl {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} (R : RotSys G) (R' : RotSys G') : Prop :=
  ∃ φ : G ≃g G', (∀ e, dmap φ (R.rot e) = R'.rot (dmap φ e)) ∨
    (∀ e, dmap φ (R.rot e) = R'.rot.symm (dmap φ e))

/-- A choice of `k` hexagonal faces for the free points: a base dart of each, in distinct faces
of size 6. The corners of the `m`-th hexagon are `A_j = ((R.face ^ j) (base m)).fst`. -/
structure HexChoice (P : PlaneGraph) (k : ℕ) where
  base : Fin k → P.G.Dart
  hex : ∀ m, Function.minimalPeriod P.R.face (base m) = 6
  distinct : ∀ m m', P.R.face.SameCycle (base m) (base m') → m = m'

/-- The points of a case: the vertices and the free points. -/
abbrev Pts (P : PlaneGraph) (k : ℕ) : Type := Fin P.n ⊕ Fin k

/-- Adjacency of points: vertices as in the graph, free points adjacent to nothing. -/
def PAdj (P : PlaneGraph) {k : ℕ} : Pts P k → Pts P k → Prop
  | .inl v, .inl w => P.G.Adj v w
  | _, _ => False

/-- Size of the face of a dart. -/
noncomputable def fsize (P : PlaneGraph) (e : P.G.Dart) : ℕ :=
  Function.minimalPeriod P.R.face e

/-! ## Assignments and the relation system -/

/-- Values of the variables of the test: the edge length, the corner at every dart, and the
distances `r m j` from the `m`-th free point to the corner `A_j` of its hexagon. -/
structure Assign (P : PlaneGraph) (k : ℕ) where
  d : ℝ
  corner : P.G.Dart → ℝ
  r : Fin k → Fin 6 → ℝ

/-- The corner of the face of `e` at its `j`-th vertex from `e.fst`. -/
noncomputable def Assign.fc {P : PlaneGraph} {k : ℕ} (A : Assign P k) (e : P.G.Dart) (j : ℕ) :
    ℝ :=
  A.corner ((P.R.face ^ j) e)

/-- (T5), the fan from `A₀` of a pentagon with corners `u₀, …, u₄`: the isosceles triangles at `A₁`
and `A₄` have bases `e = ebase d u₁`, `f = ebase d u₄` and base angles `bangle d u₁`, `bangle d u₄`,
and the middle triangle `A₀A₂A₃` has sides `e, f, d`. -/
def PentRel (d u₀ u₁ u₂ u₃ u₄ : ℝ) : Prop :=
  eta d (ebase d u₁) (ebase d u₄) ∈ Set.Icc (-1 : ℝ) 1 ∧
    eta (ebase d u₄) (ebase d u₁) d ∈ Set.Icc (-1 : ℝ) 1 ∧
    eta (ebase d u₁) (ebase d u₄) d ∈ Set.Icc (-1 : ℝ) 1 ∧
    u₀ = bangle d u₁ + gam d (ebase d u₁) (ebase d u₄) + bangle d u₄ ∧
    u₂ = bangle d u₁ + gam (ebase d u₄) (ebase d u₁) d ∧
    u₃ = bangle d u₄ + gam (ebase d u₁) (ebase d u₄) d

/-- (T6), one parity: in a hexagon with corners `u₀, …, u₅` the corners `u₁, u₃, u₅` give the sides
`ebase d u₁, ebase d u₃, ebase d u₅` of the triangle `A₀A₂A₄`, and `u₀, u₂, u₄` are sums of two base
angles and one angle of it. -/
def HexRel (d u₀ u₁ u₂ u₃ u₄ u₅ : ℝ) : Prop :=
  eta (ebase d u₃) (ebase d u₁) (ebase d u₅) ∈ Set.Icc (-1 : ℝ) 1 ∧
    eta (ebase d u₅) (ebase d u₁) (ebase d u₃) ∈ Set.Icc (-1 : ℝ) 1 ∧
    eta (ebase d u₁) (ebase d u₃) (ebase d u₅) ∈ Set.Icc (-1 : ℝ) 1 ∧
    u₀ = bangle d u₅ + gam (ebase d u₃) (ebase d u₁) (ebase d u₅) + bangle d u₁ ∧
    u₂ = bangle d u₁ + gam (ebase d u₅) (ebase d u₁) (ebase d u₃) + bangle d u₃ ∧
    u₄ = bangle d u₃ + gam (ebase d u₁) (ebase d u₃) (ebase d u₅) + bangle d u₅

/-- (T7): the least corner next to a corner `u` for which the long diagonal of the chain is at
least `d`, `L(u, d) = bangle d u + arccos (min 1 (cot d tan (ebase d u / 2)))`. -/
noncomputable def longDiag (d u : ℝ) : ℝ :=
  bangle d u + arccos (min 1 (cot d * tan (ebase d u / 2)))

/-- (T7) for two adjacent corners of a hexagon, both directions. -/
def HexDiagRel (d u₀ u₁ : ℝ) : Prop :=
  longDiag d u₀ ≤ u₁ ∧ longDiag d u₁ ≤ u₀

/-- (T8), the wheel of a free point in a hexagon with corners `u j` and distances `r j` to the
corners (indices mod 6): `d ≤ r j ≤ 3 d`, the six angles at the free point sum to `2π`, and each
corner is the sum of the two angles of the wheel triangles at it. -/
def WheelRel (d : ℝ) (u r : Fin 6 → ℝ) : Prop :=
  (∀ j, d ≤ r j ∧ r j ≤ 3 * d) ∧
    (∀ j, eta d (r j) (r (j + 1)) ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∑ j, gam d (r j) (r (j + 1)) = 2 * π ∧
    (∀ j, eta (r (j + 1)) (r j) d ∈ Set.Icc (-1 : ℝ) 1 ∧
      eta (r (j - 1)) (r j) d ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∀ j, u j = gam (r (j + 1)) (r j) d + gam (r (j - 1)) (r j) d

/-- The relation system of a case: the rows of Section 5.2 and the relations (T1) to (T8) of
Section 5.3, as the level-2 program applies them, for every face (every base dart, so every
rotation) and every free point. -/
structure RelSys (P : PlaneGraph) {k : ℕ} (H : HexChoice P k) (A : Assign P k) : Prop where
  /-- Every corner lies in `[α(d), π)` (rows (1) and (3); the program allows `π` too, and the
  strict bound keeps `rho` and `tan (x / 2)` off their junk values at `π`). -/
  corner_mem : ∀ e, alpha A.d ≤ A.corner e ∧ A.corner e < π
  /-- The corners at a vertex sum to `2π` (row (4)). -/
  vertex_sum : ∀ v, ∑ e ∈ Finset.univ.filter (fun e : P.G.Dart => e.fst = v), A.corner e = 2 * π
  /-- Triangle corners equal `α(d)` (row (1), (T3)). -/
  tri : ∀ e, fsize P e = 3 → A.corner e = alpha A.d
  /-- Rhombus: opposite corners are equal and `y = ρ_d(x)` ((T4)). -/
  rhombus : ∀ e, fsize P e = 4 → A.fc e 2 = A.fc e 0 ∧ A.fc e 1 = rho A.d (A.fc e 0)
  /-- Pentagon fans ((T1), (T2), (T5)). -/
  pent : ∀ e, fsize P e = 5 →
    PentRel A.d (A.fc e 0) (A.fc e 1) (A.fc e 2) (A.fc e 3) (A.fc e 4)
  /-- Hexagon triangles ((T1), (T2), (T6)). -/
  hex : ∀ e, fsize P e = 6 →
    HexRel A.d (A.fc e 0) (A.fc e 1) (A.fc e 2) (A.fc e 3) (A.fc e 4) (A.fc e 5)
  /-- Hexagon long diagonals ((T7)). -/
  hexDiag : ∀ e, fsize P e = 6 → HexDiagRel A.d (A.fc e 0) (A.fc e 1)
  /-- Wheels of the free points ((T8)). -/
  wheel : ∀ m, WheelRel A.d (fun j => A.fc (H.base m) j) (A.r m)

/-! ## Gluing -/

/-- Data of a gluing: a spanning tree given by the dart `par v` from the parent of each vertex
`v ≠ root` and a depth function, the reference dart at the root, and for each free point the corner
of its hexagon from which it is placed. -/
structure GlueData (P : PlaneGraph) (k : ℕ) where
  root : Fin P.n
  rootDart : P.G.Dart
  par : Fin P.n → P.G.Dart
  depth : Fin P.n → ℕ
  freeCorner : Fin k → Fin 6

/-- The tree of a gluing is a spanning tree rooted at `root`, and the reference dart of the root
starts at the root. -/
structure GlueData.Valid {P : PlaneGraph} {k : ℕ} (g : GlueData P k) : Prop where
  root_fst : g.rootDart.fst = g.root
  depth_root : g.depth g.root = 0
  par_snd : ∀ v, v ≠ g.root → (g.par v).snd = v
  par_depth : ∀ v, v ≠ g.root → g.depth (g.par v).fst + 1 = g.depth v

/-- The reference dart at `v`: the given one at the root, the dart back to the parent elsewhere. -/
def GlueData.refD {P : PlaneGraph} {k : ℕ} (g : GlueData P k) (v : Fin P.n) : P.G.Dart :=
  if v = g.root then g.rootDart else (g.par v).symm

/-- The number of rotation steps from the dart `a` to the dart `b` at the same vertex. -/
noncomputable def turnSteps {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (a b : G.Dart) : ℕ :=
  if h : ∃ s, (R.rot ^ s) a = b then Nat.find h else 0

/-- The angle turned from the dart `a` to the dart `b` at their vertex: the sum of the corners
passed. -/
noncomputable def Assign.turn {P : PlaneGraph} {k : ℕ} (A : Assign P k) (a b : P.G.Dart) : ℝ :=
  ∑ t ∈ Finset.range (turnSteps P.R a b), A.corner ((P.R.rot ^ t) a)

/-- The frames of the gluing, by recursion along the tree (`n` is the depth). -/
noncomputable def GlueData.frameN {P : PlaneGraph} {k : ℕ} (g : GlueData P k) (A : Assign P k) :
    ℕ → Fin P.n → Matrix (Fin 3) (Fin 3) ℝ
  | 0, _ => 1
  | n + 1, v =>
    if v = g.root then 1
    else g.frameN A n (g.par v).fst * stepM (A.turn (g.refD (g.par v).fst) (g.par v)) A.d

/-- The frame `F(v)` of a vertex. -/
noncomputable def GlueData.frame {P : PlaneGraph} {k : ℕ} (g : GlueData P k) (A : Assign P k)
    (v : Fin P.n) : Matrix (Fin 3) (Fin 3) ℝ :=
  g.frameN A (g.depth v) v

/-- The glued configuration: `Y(v) = F(v) e₃` for a vertex; the `m`-th free point is placed from the
corner `A_i`, `i = freeCorner m`, of its hexagon at distance `r m i`, turning from the reference
dart of `A_i` to the dart `A_i → A_{i+1}` and then by the angle `γ(r_{i+1}; r_i, d)` of the wheel
triangle at `A_i`. -/
noncomputable def glueY {P : PlaneGraph} {k : ℕ} (H : HexChoice P k) (A : Assign P k)
    (g : GlueData P k) : Pts P k → E3
  | .inl v => toEuclideanLin (g.frame A v) e3
  | .inr m =>
    toEuclideanLin
      (g.frame A ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst *
        rotZ (A.turn (g.refD ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)).fst)
            ((P.R.face ^ ((g.freeCorner m : Fin 6) : ℕ)) (H.base m)) +
          gam (A.r m (g.freeCorner m + 1)) (A.r m (g.freeCorner m)) A.d) *
        rotY (A.r m (g.freeCorner m))) e3

/-! ## Pair and Local -/

/-- Pair: two points not joined by an edge at chord distance below `2 sin (d/2)`. -/
def PairFires (P : PlaneGraph) {k : ℕ} (A : Assign P k) (Y : Pts P k → E3) : Prop :=
  ∃ a b, a ≠ b ∧ ¬ PAdj P a b ∧ ‖Y a - Y b‖ < 2 * sin (A.d / 2)

/-- A labelled frame configuration with its set of contact pairs `(i, j)`, `i < j`. -/
structure Frame where
  p : Fin 15 → E3
  S : Finset (Fin 15 × Fin 15)

/-- The radius of Local, `1.04·10⁻³` (Theorem 4.1). -/
noncomputable def rLocal : ℝ := 1.04e-3

/-- Local: every point is within `rLocal` of an isometric image of a frame configuration of `F`,
under a bijection of the points with the fifteen frame points. -/
def LocalFires (F : Set Frame) {α : Type} (Y : α → E3) : Prop :=
  ∃ q ∈ F, ∃ O : E3 ≃ₗᵢ[ℝ] E3, ∃ j : α ≃ Fin 15, ∀ a, ‖Y a - O (q.p (j a))‖ ≤ rLocal

/-! ## Realisations (Definition 5.1) -/

/-- A realisation of the case `(P, H)` with edge length `d` (Definition 5.1): unit vectors;
adjacent vertices at distance `d`; the drawing has the rotation system `P.R` (`IsAngular`) and
convex faces (`StrictSupportFace`) with corners in `[α(d), π)`; distinct points at distance at
least `d`; each free point strictly inside its hexagon (on the inner side of every side). -/
structure Realisation (P : PlaneGraph) {k : ℕ} (H : HexChoice P k) (d : ℝ)
    (x : Pts P k → E3) : Prop where
  d_mem : 0 < d ∧ d < π / 2
  unit : ∀ a, ‖x a‖ = 1
  edge : ∀ v w, P.G.Adj v w → sdist (x (.inl v)) (x (.inl w)) = d
  angular : IsAngular P.R (fun v => x (.inl v))
  convex : StrictSupportFace P.R (fun v => x (.inl v))
  corners : ∀ e : P.G.Dart,
    alpha d ≤ ocorner (x (.inl e.fst)) (x (.inl e.snd)) (x (.inl (P.R.rot e).snd)) ∧
      ocorner (x (.inl e.fst)) (x (.inl e.snd)) (x (.inl (P.R.rot e).snd)) < π
  sep : ∀ a b, a ≠ b → d ≤ sdist (x a) (x b)
  inside : ∀ m (j : ℕ), 0 < ⟪cross (x (.inl ((P.R.face ^ j) (H.base m)).fst))
      (x (.inl ((P.R.face ^ j) (H.base m)).snd)), x (.inr m)⟫

/-- The assignment read from a configuration: its corners and the distances of the free points to
the corners of their hexagons. -/
noncomputable def assignOf (P : PlaneGraph) {k : ℕ} (H : HexChoice P k) (d : ℝ)
    (x : Pts P k → E3) : Assign P k where
  d := d
  corner e := ocorner (x (.inl e.fst)) (x (.inl e.snd)) (x (.inl (P.R.rot e).snd))
  r m j := sdist (x (.inr m)) (x (.inl ((P.R.face ^ (j : ℕ)) (H.base m)).fst))

end Tammes15
