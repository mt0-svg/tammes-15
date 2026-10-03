import Tammes15.Hyps.Computations
import Tammes15.Draw.Structure
import Tammes15.Draw.Exist
import Tammes15.Draw.Realise
import Tammes15.Numerics.Root
import Tammes15.Trigrows.Realise
import Tammes15.Fans.Realise
import Tammes15.Glue.Reconstruct
import Tammes15.Geom.T8

/-!
# The interfaces the capstone uses

Every theorem of this file is an interface: a statement that another part of the package proves
(named in each docstring), stated in the objects of `Tammes15.Hyps.Case`. Seven are closed by the
theorem of that part with the same statement, named in their docstrings; the other two,
`vertexSum_of_realisation` and `dlo_lt_arccos_root`, by `vertexSum_realisation`, which needs fewer
hypotheses, and by `Numerics.dlo_lt_arccos_quintic_root`. The interfaces of the drawing layer
(`structure_theorem`, `exists_isGreatest_config`, `achievable_iff_nonempty_config`,
`contactGraph_adj_iff`) are used from `Tammes15.Draw.Structure` and `Tammes15.Draw.Exist` directly.

Common hypotheses: `P` is a plane graph of the class, `x` a realisation of the case `(P, H)` with
edge length `d ∈ [dlo, dhi]`, `A = assignOf P H d x` its assignment.
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-! ## Margin -/

/-- `dlo = 53.65785°` lies below `ψ* = arccos u` (`ψ* = 53.6578501299…°`; the margin is about
`1.3·10⁻⁷` degrees), from `Numerics.dlo_lt_arccos_quintic_root`. -/
theorem dlo_lt_arccos_root (u : ℝ) (h1 : 1 / 2 < u) (h2 : u < 7 / 10) (h0 : quintic u = 0) :
    dlo < arccos u := by
  unfold dlo
  exact Numerics.dlo_lt_arccos_quintic_root u h1 h2 (by simpa [quintic] using h0)

/-! ## The relation system of a realisation (Sections 6.1 and 6.2) -/

section Relations

variable {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ} {x : Pts P k → E3}

/-- Row (4): the corners at a vertex sum to `2π`. Proved in Draw as
`vertexSum_realisation` (Draw/Realise). -/
theorem vertexSum_of_realisation (hP : InClass P) (_hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (v : Fin P.n) :
    ∑ e ∈ Finset.univ.filter (fun e : P.G.Dart => e.fst = v), (assignOf P H d x).corner e =
      2 * π :=
  vertexSum_realisation hP hx v

/-- (T3): the corners of a triangular face equal `α(d)`, from Trigrows, with the
corner of a face as an angle of the spherical triangle (Fans). Proved as
`tri_of_realisation_proof` (Trigrows/Realise). -/
theorem tri_of_realisation (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 3) :
    (assignOf P H d x).corner e = alpha d :=
  tri_of_realisation_proof hP hd hx e he

/-- (T4): a quadrilateral face is a rhombus with opposite corners equal and `y = ρ_d(x)`.
Proved as `rhombus_of_realisation_proof` (Trigrows/Realise). -/
theorem rhombus_of_realisation (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 4) :
    (assignOf P H d x).fc e 2 = (assignOf P H d x).fc e 0 ∧
      (assignOf P H d x).fc e 1 = rho d ((assignOf P H d x).fc e 0) :=
  rhombus_of_realisation_proof hP hd hx e he

/-- (T5): the fan of a pentagonal face from each corner. Proved as
`pent_of_realisation_proof` (Fans/Realise). -/
theorem pent_of_realisation (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 5) :
    PentRel d ((assignOf P H d x).fc e 0) ((assignOf P H d x).fc e 1)
      ((assignOf P H d x).fc e 2) ((assignOf P H d x).fc e 3) ((assignOf P H d x).fc e 4) :=
  pent_of_realisation_proof hP hd hx e he

/-- (T6): the alternate-corner triangle of a hexagonal face. Proved as
`hex_of_realisation_proof` (Fans/Realise). -/
theorem hex_of_realisation (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 6) :
    HexRel d ((assignOf P H d x).fc e 0) ((assignOf P H d x).fc e 1)
      ((assignOf P H d x).fc e 2) ((assignOf P H d x).fc e 3) ((assignOf P H d x).fc e 4)
      ((assignOf P H d x).fc e 5) :=
  hex_of_realisation_proof hP hd hx e he

/-- (T7): the long diagonals of a hexagonal face are at least `d`, from Trigrows (the
core inequality), with the face corners as chain angles (Fans). Proved as
`hexDiag_of_realisation_proof` (Trigrows/Realise). -/
theorem hexDiag_of_realisation (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 6) :
    HexDiagRel d ((assignOf P H d x).fc e 0) ((assignOf P H d x).fc e 1) :=
  hexDiag_of_realisation_proof hP hd hx e he

/-- (T8): the wheel of each free point in its hexagon, from Geom (the wheel), with
`r ≤ 3d` from Rattlers. Proved as `Geom.wheel_of_realisation_proof` (Geom/T8). -/
theorem wheel_of_realisation (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (m : Fin k) :
    WheelRel d (fun j => (assignOf P H d x).fc (H.base m) j) ((assignOf P H d x).r m) :=
  Geom.wheel_of_realisation_proof hP hd hx m

end Relations

/-! ## Gluing (Section 6.3) -/

/-- Reconstruction: the configuration glued from the assignment of a realisation, along any
valid tree and from any corners of the hexagons, is the realisation moved by a linear isometry.
Proved as `glue_congruent_proof` (Glue/Reconstruct). -/
theorem glue_congruent {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ} {x : Pts P k → E3}
    (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi) (hx : Realisation P H d x) (g : GlueData P k)
    (hg : g.Valid) :
    ∃ O : E3 ≃ₗᵢ[ℝ] E3, ∀ a, glueY H (assignOf P H d x) g a = O (x a) :=
  glue_congruent_proof hP hd hx g hg

end Tammes15
