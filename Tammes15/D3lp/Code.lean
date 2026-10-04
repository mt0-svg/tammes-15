import Tammes15.Hyps.Case
import Tammes15.D3lp.Lin

namespace Tammes15.D3lp

open Tammes15

def lane (x i : ℕ) : ℕ := (x >>> (8 * i)) % 256

structure GCode where
  D : ℕ
  face : ℕ
  fst : ℕ
  deriving Repr, DecidableEq

def GCode.faceAt (c : GCode) (i : ℕ) : ℕ := lane c.face i

def GCode.fstAt (c : GCode) (i : ℕ) : ℕ := lane c.fst i

def GCode.faceIter (c : GCode) (i : ℕ) : ℕ → ℕ
  | 0 => i
  | j + 1 => c.faceAt (c.faceIter i j)

def GCode.periodGo (c : GCode) (i : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, cur, t => if c.faceAt cur = i then t else c.periodGo i fuel (c.faceAt cur) (t + 1)

def GCode.period (c : GCode) (i : ℕ) : ℕ := c.periodGo i 6 i 1

structure Matches (P : PlaneGraph) (c : GCode) (lab : P.G.Dart ≃ Fin c.D) : Prop where
  face : ∀ e, c.faceAt (lab e) = lab (P.R.face e)
  fst : ∀ e, c.fstAt (lab e) = (e.fst : ℕ)

noncomputable def vars {P : PlaneGraph} {k D : ℕ} (lab : P.G.Dart ≃ Fin D) (A : Assign P k) :
    ℕ → ℝ
  | 0 => alpha A.d
  | i + 1 => if h : i < D then A.corner (lab.symm ⟨i, h⟩) else 0

def dv (i : ℕ) : ℕ := i + 1

structure CutRow where
  w : List ℤ
  lo : ℤ
  hi : ℤ
  deriving Repr, DecidableEq

structure Params where
  S : ℕ
  alo : ℤ
  ahi : ℤ
  shi : ℤ
  pihi : ℤ
  twopilo : ℤ
  twopihi : ℤ
  pent : List CutRow
  hex : List CutRow
  deriving Repr

inductive RowId where

  | alpha (up : Bool)

  | corner (i : ℕ) (up : Bool)

  | vertex (v : ℕ) (up : Bool)

  | tri (i : ℕ) (up : Bool)

  | rhOpp (i : ℕ) (up : Bool)

  | rhLe (i : ℕ)

  | rhSum (i : ℕ) (up : Bool)

  | pent (k i : ℕ) (rev up : Bool)

  | hex (k i : ℕ) (rev up : Bool)
  deriving Repr, DecidableEq

def RowId.encode : RowId → ℕ
  | .alpha up => 0 + 16 * up.toNat
  | .corner i up => 1 + 16 * up.toNat + 64 * i
  | .vertex v up => 2 + 16 * up.toNat + 64 * v
  | .tri i up => 3 + 16 * up.toNat + 64 * i
  | .rhOpp i up => 4 + 16 * up.toNat + 64 * i
  | .rhLe i => 5 + 64 * i
  | .rhSum i up => 6 + 16 * up.toNat + 64 * i
  | .pent k i rev up => 7 + 16 * up.toNat + 32 * rev.toNat + 64 * i + 16384 * k
  | .hex k i rev up => 8 + 16 * up.toNat + 32 * rev.toNat + 64 * i + 16384 * k

def RowId.decode (n : ℕ) : Option RowId :=
  let kind := n % 16
  let up := (n / 16) % 2 == 1
  let rev := (n / 32) % 2 == 1
  let i := (n / 64) % 256
  let k := n / 16384
  if kind = 0 then some (.alpha up)
  else if kind = 1 then some (.corner i up)
  else if kind = 2 then some (.vertex i up)
  else if kind = 3 then some (.tri i up)
  else if kind = 4 then some (.rhOpp i up)
  else if kind = 5 then some (.rhLe i)
  else if kind = 6 then some (.rhSum i up)
  else if kind = 7 then some (.pent k i rev up)
  else if kind = 8 then some (.hex k i rev up)
  else none

def listGet {α : Type} : List α → ℕ → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, k + 1 => listGet l k

def cutTerms (c : GCode) (m i : ℕ) (rev : Bool) (sgn : ℤ) : ℕ → List ℤ → List (ℕ × ℤ)
  | _, [] => []
  | j, w :: ws =>
    (dv (c.faceIter i (if rev then (m - j) % m else j)), sgn * w) :: cutTerms c m i rev sgn (j + 1) ws

def vertexTerms (c : GCode) (v : ℕ) (s : ℤ) : List (ℕ × ℤ) :=
  ((List.range c.D).filter fun i => c.fstAt i == v).map fun i => (dv i, s)

def cutRow (c : GCode) (m : ℕ) (tab : List CutRow) (k i : ℕ) (rev up : Bool) : Option Row :=
  match listGet tab k with
  | none => none
  | some cr =>
    if cr.w.length = m then
      some (if up then ⟨cutTerms c m i rev 1 0 cr.w, cr.hi⟩ else ⟨cutTerms c m i rev (-1) 0 cr.w, -cr.lo⟩)
    else none

def rowOf (c : GCode) (p : Params) : RowId → Option Row
  | .alpha false => some ⟨[(0, -(p.S : ℤ))], -p.alo⟩
  | .alpha true => some ⟨[(0, (p.S : ℤ))], p.ahi⟩
  | .corner i false => if i < c.D then some ⟨[(0, 1), (dv i, -1)], 0⟩ else none
  | .corner i true => if i < c.D then some ⟨[(dv i, (p.S : ℤ))], p.pihi⟩ else none
  | .vertex v up =>
    if ((List.range c.D).filter fun i => c.fstAt i == v).isEmpty then none
    else if up then some ⟨vertexTerms c v (p.S : ℤ), p.twopihi⟩
    else some ⟨vertexTerms c v (-(p.S : ℤ)), -p.twopilo⟩
  | .tri i up =>
    if i < c.D ∧ c.period i = 3 then
      some (if up then ⟨[(0, -1), (dv i, 1)], 0⟩ else ⟨[(0, 1), (dv i, -1)], 0⟩)
    else none
  | .rhOpp i up =>
    if i < c.D ∧ c.period i = 4 then
      some (if up then ⟨[(dv i, -1), (dv (c.faceIter i 2), 1)], 0⟩
        else ⟨[(dv i, 1), (dv (c.faceIter i 2), -1)], 0⟩)
    else none
  | .rhLe i => if i < c.D ∧ c.period i = 4 then some ⟨[(0, -2), (dv i, 1)], 0⟩ else none
  | .rhSum i up =>
    if i < c.D ∧ c.period i = 4 then
      some (if up then ⟨[(dv i, (p.S : ℤ)), (dv (c.faceIter i 1), (p.S : ℤ))], p.shi⟩
        else ⟨[(0, 3), (dv i, -1), (dv (c.faceIter i 1), -1)], 0⟩)
    else none
  | .pent k i rev up => if i < c.D ∧ c.period i = 5 then cutRow c 5 p.pent k i rev up else none
  | .hex k i rev up => if i < c.D ∧ c.period i = 6 then cutRow c 6 p.hex k i rev up else none

end Tammes15.D3lp
