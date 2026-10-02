import Std.Data.HashMap
import Floats

/-!
# The Lean side of the differential test of Prims.lean (Section 10.4 of the paper)

Reads on stdin the stream of the Rust driver (`difftest.rs`, format in its header), and for each
case evaluates the primitive of `PrimsQ` (the computable copy of Prims.lean, which Commute.lean
proves equal to Prims.lean at the arithmetic `lift R`) on the same inputs, with the arithmetic `R`
read from the case's log: each operation of `RndQ` looks its arguments up in the table of the
calls the program made, and panics (message `MISS`, on stderr) when the program never made that
call. The constants `piLo`, `piHi`, `twoPiLo`, `twoPiHi` are those of the `P` line.

It writes on stdout its own stream, one line `L prim id result` per case in the format of the `R`
lines, and in the report file (first argument) every mismatch between its result and the
program's, every conflicting log entry, and per primitive the number of cases, matches,
mismatches and the summary line `S` of the driver.

A float is compared exactly: the program's value read as a rational (`ofBits`), written back as
its bits when it is a double (`tok`), as `q<num>/<den>` otherwise.
-/

open Tammes15.Contractors.Q

namespace DiffTest

/-! ## The arithmetic of a case -/

abbrev Key := Nat × FlQ × FlQ × FlQ × FlQ

abbrev Table := Std.HashMap Key (FlQ × FlQ)

def look (t : Table) (tag : String) (k : Key) : FlQ × FlQ :=
  match t[k]? with
  | some v => v
  | none =>
    panic! s!"MISS {tag} op {k.1} {tok k.2.1} {tok k.2.2.1} {tok k.2.2.2.1} {tok k.2.2.2.2}"

def iv2 (t : Table) (tag : String) (op : Nat) (I J : IvQ) : IvQ :=
  let r := look t tag (op, I.lo, I.hi, J.lo, J.hi)
  ⟨r.1, r.2⟩

def iv1 (t : Table) (tag : String) (op : Nat) (I : IvQ) : IvQ :=
  let r := look t tag (op, I.lo, I.hi, .fin 0, .fin 0)
  ⟨r.1, r.2⟩

def pt2 (t : Table) (tag : String) (op : Nat) (a b : FlQ) : FlQ :=
  (look t tag (op, a, b, .fin 0, .fin 0)).1

structure Consts where
  piLo : Rat
  piHi : Rat
  twoPiLo : Rat
  twoPiHi : Rat

/-- The arithmetic read from the log `t` of a case. Codes in the order of `dtlog::OP_NAMES`. -/
def mkR (t : Table) (tag : String) (c : Consts) : RndQ where
  add := iv2 t tag 0
  sub := iv2 t tag 1
  mul := iv2 t tag 2
  div := iv2 t tag 3
  cos := iv1 t tag 4
  sin := iv1 t tag 5
  acos := iv1 t tag 6
  asin := iv1 t tag 7
  atan := iv1 t tag 8
  tan := iv1 t tag 9
  addDn := pt2 t tag 10
  addUp := pt2 t tag 11
  subDn := pt2 t tag 12
  subUp := pt2 t tag 13
  mulDn := pt2 t tag 14
  mulUp := pt2 t tag 15
  divDn := pt2 t tag 16
  divUp := pt2 t tag 17
  piLo := c.piLo
  piHi := c.piHi
  twoPiLo := c.twoPiLo
  twoPiHi := c.twoPiHi

/-! ## Inputs and results -/

def ivAt (t : Array String) (p : Nat) : IvQ := ⟨ofHex t[p]!, ofHex t[p + 1]!⟩

/-- A box at position `p`: its size `n`, then `n` pairs of ends; the box, `n` and the next
position. -/
def boxAt (t : Array String) (p : Nat) : BoxQ Nat × Nat × Nat :=
  let n := t[p]!.toNat!
  let lo := (Array.range n).map fun i => (ofHex t[p + 1 + 2 * i]!).toQ
  let hi := (Array.range n).map fun i => (ofHex t[p + 2 + 2 * i]!).toQ
  (⟨fun i => lo.getD i 0, fun i => hi.getD i 0⟩, n, p + 1 + 2 * n)

def natAt (t : Array String) (p : Nat) : Nat := t[p]!.toNat!

def intAt (t : Array String) (p : Nat) : Int := t[p]!.toInt!

def tokIv (I : IvQ) : String := tok I.lo ++ " " ++ tok I.hi

def resBox (n : Nat) : Option (BoxQ Nat) → String
  | none => "0"
  | some B => (List.range n).foldl (fun s i => s ++ " " ++ tok (.fin (B.lo i)) ++ " " ++
      tok (.fin (B.hi i))) "1"

def resIv (I : IvQ) : String := "0 " ++ tokIv I

def resOpt : Option IvQ → String
  | none => "0"
  | some I => "1 " ++ tokIv I

def resIvs (l : List IvQ) : String := l.foldl (fun s I => s ++ " " ++ tokIv I) "0"

def resFl (x : FlQ) : String := "0 " ++ tok x

def fin3 : List (Fin 3) := [0, 1, 2]

/-- The result of the primitive `prim` at the inputs `t`, in the format of the `R` lines. -/
def evalCase (R : RndQ) (prim : String) (t : Array String) : String :=
  match prim with
  | "nar" =>
    let (B, n, p) := boxAt t 0
    resBox n (nar B (natAt t p) (ivAt t (p + 1)))
  | "isoBase" => resIv (isoBase R (ivAt t 0) (ivAt t 2))
  | "isoAngle" => resIv (isoAngle R (ivAt t 0) (ivAt t 2))
  | "longdiagLb" => resFl (longdiagLb R (ivAt t 0) (ivAt t 2))
  | "triAngleSt" =>
    match triAngleSt R (ivAt t 0) (ivAt t 2) (ivAt t 4) with
    | .ok v => "0 " ++ tokIv v
    | .error v => "1 " ++ tokIv v
  | "triAngle" => resOpt (triAngle R (ivAt t 0) (ivAt t 2) (ivAt t 4))
  | "triAngleC" => resIv (triAngleC R (ivAt t 0) (ivAt t 2) (ivAt t 4))
  | "alphaIv" => resIv (alphaIv R (ivAt t 0))
  | "alphaInvIv" => resIv (alphaInvIv R (ivAt t 0))
  | "rhoIv" => resIv (rhoIv R (ivAt t 0) (ivAt t 2))
  | "rhombusD" => resOpt (rhombusD R (ivAt t 0) (ivAt t 2))
  | "side" => resOpt (side R (ivAt t 0) (ivAt t 2) (ivAt t 4))
  | "cornerEnds" =>
    let e := cornerEnds R (ivAt t 0)
    resIvs [e.1, e.2]
  | "decDir" => toString (decDir R (ivAt t 0) (ivAt t 2) (ivAt t 4) (ivAt t 6))
  | "monoBounds2" =>
    let d := ivAt t 0
    let inp : Fin 2 → IvQ := fun j => ivAt t (2 + 6 * j.val)
    let ends : Fin 2 → IvQ × IvQ := fun j => (ivAt t (4 + 6 * j.val), ivAt t (6 + 6 * j.val))
    let dirs : Fin 3 → Fin 2 → Int := fun a b => intAt t (14 + 2 * a.val + b.val)
    resIvs (fin3.map (monoBounds inp ends dirs (pentEvalC R d)))
  | "monoBounds3" =>
    let d := ivAt t 0
    let inp : Fin 3 → IvQ := fun j => ivAt t (2 + 6 * j.val)
    let ends : Fin 3 → IvQ × IvQ := fun j => (ivAt t (4 + 6 * j.val), ivAt t (6 + 6 * j.val))
    let dirs : Fin 3 → Fin 3 → Int := fun a b => intAt t (20 + 3 * a.val + b.val)
    resIvs (fin3.map (monoBounds inp ends dirs (hexEvalC R d)))
  | "pentEvalC" =>
    let d := ivAt t 0
    resIvs (fin3.map (pentEvalC R d (fun j => ivAt t (2 + 2 * j.val))))
  | "hexEvalC" =>
    let d := ivAt t 0
    resIvs (fin3.map (hexEvalC R d (fun j => ivAt t (2 + 2 * j.val))))
  | "cmin" => resFl (cmin R (ofHex t[0]!).toQ (ofHex t[1]!).toQ (ofHex t[2]!).toQ)
  | "cmax" => resFl (cmax R (ofHex t[0]!).toQ (ofHex t[1]!).toQ (ofHex t[2]!).toQ)
  | "alphaStep" =>
    let (B, n, p) := boxAt t 0
    resBox n (alphaStep R B 0 (natAt t p))
  | "alphaInvStep" =>
    let (B, n, p) := boxAt t 0
    resBox n (alphaInvStep R B 0 (natAt t p))
  | "rhoStep" | "rhoDStep" | "diagFwdStep" | "diagBwdStep" =>
    let (B, n, p) := boxAt t 0
    let (u0, u1, di) := (natAt t p, natAt t (p + 1), natAt t (p + 2))
    let v : Nat → Nat := fun j => if j = 0 then u0 else u1
    let r := match prim with
      | "rhoStep" => rhoStep R B v di
      | "rhoDStep" => rhoDStep R B v di
      | "diagFwdStep" => diagFwdStep R B v di
      | _ => diagBwdStep R B v di
    resBox n r
  | "pentStep" =>
    let (B, n, p) := boxAt t 0
    let u := fun j => natAt t (p + j)
    let rot := natAt t (p + 5)
    resBox n (pentStep R B (fun j => u ((rot + j) % 5)) (natAt t (p + 6)))
  | "hexStep" =>
    let (B, n, p) := boxAt t 0
    let u := fun j => natAt t (p + j)
    let par := natAt t (p + 6)
    resBox n (hexStep R B (fun j => u ((j + par) % 6)) (natAt t (p + 7)))
  | "wheelStep" =>
    let (B, n, p) := boxAt t 0
    let u := fun j => natAt t (p + j)
    let r0 := natAt t (p + 6)
    resBox n (wheelStep R (fun j => u (j % 6)) (fun i => r0 + i.val) (natAt t (p + 7)) B)
  | "rowStep" =>
    let (B, n, p) := boxAt t 0
    let k := natAt t p
    let terms := (List.range k).map fun j => (natAt t (p + 1 + 2 * j),
      (ofHex t[p + 2 + 2 * j]!).toQ)
    let row : RowQ Nat := ⟨terms, ofHex t[p + 1 + 2 * k]!, ofHex t[p + 2 + 2 * k]!⟩
    resBox n (rowStep R row B)
  | _ => "UNKNOWN"

/-! ## The loop -/

structure Count where
  cases : Nat := 0
  same : Nat := 0
  diff : Nat := 0
  conflicts : Nat := 0

def words (s : String) : Array String :=
  ((s.splitOn " ").filter (· != "")).toArray

partial def loop (inp out : IO.FS.Stream) (rep : IO.FS.Handle) (c : Consts)
    (counts : Std.HashMap String Count) (order : Array String) (prim : String) (id : String)
    (input : Array String) (tab : Table) (res : String) (summary : Array String) :
    IO (Consts × Std.HashMap String Count × Array String × Array String) := do
  let line ← inp.getLine
  if line.isEmpty then return (c, counts, order, summary)
  let line := line.trimAsciiEnd.toString
  let w := words line
  match w[0]? with
  | some "P" =>
    let q := fun i => (ofHex w[i]!).toQ
    loop inp out rep ⟨q 1, q 2, q 3, q 4⟩ counts order prim id input tab res summary
  | some "C" =>
    let p := w[1]!
    let order := if counts.contains p then order else order.push p
    let counts := if counts.contains p then counts else counts.insert p {}
    loop inp out rep c counts order p w[2]! #[] {} "" summary
  | some "I" => loop inp out rep c counts order prim id (w.extract 1 w.size) tab res summary
  | some "O" =>
    let k : Key := (w[1]!.toNat!, ofHex w[2]!, ofHex w[3]!, ofHex w[4]!, ofHex w[5]!)
    let v := (ofHex w[6]!, ofHex w[7]!)
    match tab[k]? with
    | some v' =>
      if v' != v then
        rep.putStrLn s!"CONFLICT {prim} {id} {line}"
        let cnt := counts.getD prim {}
        loop inp out rep c (counts.insert prim { cnt with conflicts := cnt.conflicts + 1 }) order
          prim id input tab res summary
      else loop inp out rep c counts order prim id input tab res summary
    | none => loop inp out rep c counts order prim id input (tab.insert k v) res summary
  | some "R" =>
    loop inp out rep c counts order prim id input tab (" ".intercalate (w.extract 1 w.size).toList)
      summary
  | some "E" =>
    let l := evalCase (mkR tab s!"{prim} {id}" c) prim input
    out.putStrLn s!"L {prim} {id} {l}"
    let cnt := counts.getD prim {}
    let cnt := { cnt with cases := cnt.cases + 1 }
    let cnt ← if l == res then pure { cnt with same := cnt.same + 1 } else do
      rep.putStrLn s!"MISMATCH {prim} {id}\n  input {" ".intercalate input.toList}\n  rust  {res}\n  lean  {l}"
      pure { cnt with diff := cnt.diff + 1 }
    loop inp out rep c (counts.insert prim cnt) order prim id input tab res summary
  | some "S" => loop inp out rep c counts order prim id input tab res (summary.push line)
  | _ =>
    rep.putStrLn s!"BADLINE {line}"
    loop inp out rep c counts order prim id input tab res summary

end DiffTest

open DiffTest in
def main (args : List String) : IO UInt32 := do
  let some repPath := args.head? | do IO.eprintln "usage: difftest REPORT"; return 2
  let rep ← IO.FS.Handle.mk repPath .write
  let out ← IO.getStdout
  let inp ← IO.getStdin
  let (_, counts, order, summary) ← loop inp out rep ⟨0, 0, 0, 0⟩ {} #[] "" "" #[] {} "" #[]
  rep.putStrLn "# per primitive: cases, equal results, mismatches, conflicting log entries"
  let mut total : Count := {}
  for p in order do
    let cnt := counts.getD p {}
    rep.putStrLn s!"T {p} {cnt.cases} {cnt.same} {cnt.diff} {cnt.conflicts}"
    total := { cases := total.cases + cnt.cases, same := total.same + cnt.same,
               diff := total.diff + cnt.diff, conflicts := total.conflicts + cnt.conflicts }
  rep.putStrLn s!"TOTAL {total.cases} {total.same} {total.diff} {total.conflicts}"
  rep.putStrLn "# the driver's summary: prim cases conflicts flips entries outcome:count"
  for s in summary do rep.putStrLn s
  rep.flush
  return 0
