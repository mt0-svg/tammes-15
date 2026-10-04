import Tammes15.D3Kernel.Kinds.Keys
import Mathlib.Data.List.Sublists

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Walk

def nV (c : GCode) : ℕ := (List.range c.D).foldl (fun a i => max a (c.fstAt i + 1)) 0

def vertsOK (c : GCode) (n : ℕ) : Bool :=
  (List.range c.D).all (fun i => decide (c.fstAt i < n)) && (List.range c.D).any (fun i => c.fstAt i + 1 == n)

def canon (c : GCode) (i : ℕ) : Bool :=
  decide (i < c.D) && c.faceIter i 6 == i && (List.range 5).all (fun j => decide (i < c.faceIter i (j + 1)))

def canonList (c : GCode) : List ℕ := (List.range c.D).filter (canon c)

def hrep (c : GCode) (i : ℕ) : ℕ :=
  min i (min (c.faceIter i 1) (min (c.faceIter i 2) (min (c.faceIter i 3)
    (min (c.faceIter i 4) (c.faceIter i 5)))))

def repsOf (c : GCode) (g k : ℕ) : List ℕ := (List.range k).map (fun m => hrep c (Ctx.base g m))

def cALO : ℕ := 5485728400226463897

def cAHI : ℕ := 5572325549701602698

def c2AHI : ℕ := 11144651099403205396

def cPI : ℕ := 14488038916154245685

def cDLO : ℕ := 4318872327539817176

def cDHI : ℕ := 4561446368004038610

def c3DHI : ℕ := 13684339104012115830

def varOK (g box v : ℕ) : Bool :=
  let lo := bnd box (2 * v)
  let hi := bnd box (2 * v + 1)
  let m := Ctx.mean g v
  kgood lo && kgood hi &&
    (if m = 0 then decide (kfix lo ≤ cALO) && decide (cAHI ≤ kfix hi)
    else if m = 1 then decide (kfix lo ≤ cDLO) && decide (cDHI ≤ kfix hi)
    else if m < 258 then decide (m - 2 < Ctx.D g) && decide (kfix lo ≤ cALO) &&
      (decide (cPI ≤ kfix hi) || ((Ctx.code g).period (m - 2) == 4 && decide (c2AHI ≤ kfix hi)))
    else decide ((m - 258) / 6 < Ctx.k g) && decide (kfix lo ≤ cDLO) && decide (c3DHI ≤ kfix hi))

def boxOK (g box : ℕ) : Bool := (List.range (Ctx.nv g)).all (varOK g box)

def rootOK (c : GCode) (k g box : ℕ) : Bool :=
  Ctx.D g == c.D && Ctx.face g == c.face && Ctx.fst g == c.fst && Ctx.k g == k &&
    (List.range k).all (fun m => decide (Ctx.base g m < c.D)) && boxOK g box

def cover (c : GCode) (R : List ℕ) : Bool :=
  vertsOK c (nV c) && decide (nV c ≤ 15) &&
    (rootPairs R).all (fun p => rootOK c (15 - nV c) p.1 p.2) &&
    (List.sublistsLen (15 - nV c) (canonList c)).all
      (fun s => (rootPairs R).any (fun p => repsOf c p.1 (15 - nV c) == s))

end Tammes15.D3Kernel.Kinds
