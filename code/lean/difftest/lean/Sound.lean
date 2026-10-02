import Std.Data.HashMap
import Floats

/-!
# Exact check of the logged arithmetic against `Rnd.Sound` (Section 10.4 of the paper)

Reads the stream of the Rust driver on stdin and checks, for every logged call of a basic
operation, the instance of the field of `Rnd.Sound` (Arith.lean) about that call, in exact
rational arithmetic. A field quantifies over reals `x, y`; at a call with arguments `I, J` (or
`a, b`) and result `K` (or `r`) it says:

* `add`, `sub`, `mul`, `div`: `K` contains `x ∘ y` for all reals `x ∈ I`, `y ∈ J` (`y ≠ 0` for
  `div`). The set of these values is empty, or has its infimum and supremum (in the extended
  rationals) among the values at the four corners, read as limits (`0 · ∞ = 0` for `mul`; for
  `div`, `p / ±∞ = 0` and an infinite numerator gives an infinite quotient). So the field holds at
  the call iff the set is empty or `K.lo ≤ inf` and `sup ≤ K.hi` (an infinite bound asks for the
  infinite end). `div` with `0 ∈ J` is checked only when `K` is the whole line, which is what
  ivt.rs returns there; otherwise it is reported unchecked.
* `add_lo`: `K.lo ≤ x + y` for all reals `x ≥ I.lo`, `y ≥ J.lo`.
* `addDn`, `addUp`, `subDn`, `subUp`: the directed bound over all reals on the given side of `a`
  and `b`; `subDn_ninf`, `subUp_inf`, `subDn_nan`, `subUp_nan` at the calls they name.
* `mulDn`, `mulUp`, `divDn`, `divUp`: the directed bound at finite arguments (`b ≠ 0` for the
  divisions); the fields say nothing at the other arguments.

The transcendental operations (`cos` to `tan`) and the constants (`piLo` to `twoPiHi`) are not
checked here. Output, on stdout: a line `FAIL` per failed instance, then per operation the
number of calls, of instances checked, of instances that hold vacuously, of failures and of
unchecked calls.
-/

open Tammes15.Contractors.Q

namespace DiffTest

/-- An element of the real line exists between `lo` and `hi`. -/
def nonempty (I : IvQ) : Bool :=
  match I.lo, I.hi with
  | .fin p, .fin q => decide (p ≤ q)
  | .bot, .fin _ | .bot, .top | .fin _, .top => true
  | _, _ => false

def sgn (p : Rat) : Int := if p > 0 then 1 else if p < 0 then -1 else 0

/-- An infinity of sign `s` (`0` gives `0`). -/
def infOf (s : Int) : FlQ := if s > 0 then .top else if s < 0 then .bot else .fin 0

def sgnF : FlQ → Int
  | .fin p => sgn p
  | .top => 1
  | .bot => -1
  | .nan => 0

/-- Sum of extended rationals with no opposite infinities. -/
def eadd : FlQ → FlQ → FlQ
  | .fin p, .fin q => .fin (p + q)
  | .fin _, b => b
  | a, _ => a

def eneg : FlQ → FlQ
  | .fin p => .fin (-p)
  | .top => .bot
  | .bot => .top
  | .nan => .nan

/-- Product, `0 · ∞ = 0`. -/
def emul : FlQ → FlQ → FlQ
  | .fin p, .fin q => .fin (p * q)
  | a, b => infOf (sgnF a * sgnF b)

/-- Quotient by a nonzero `b`, read as a limit: `p / ±∞ = 0`, an infinite numerator wins. -/
def ediv : FlQ → FlQ → FlQ
  | .fin p, .fin q => .fin (p / q)
  | .fin _, _ => .fin 0
  | a, b => infOf (sgnF a * sgnF b)

def emin (a b : FlQ) : FlQ := if FlQ.ble a b then a else b
def emax (a b : FlQ) : FlQ := if FlQ.ble a b then b else a

def corners (f : FlQ → FlQ → FlQ) (I J : IvQ) : FlQ × FlQ :=
  let c := [f I.lo J.lo, f I.lo J.hi, f I.hi J.lo, f I.hi J.hi]
  (c.foldl emin .top, c.foldl emax .bot)

inductive Verdict
  | holds
  | vacuous
  | fails
  | unchecked
  deriving BEq

def bounds (K : IvQ) (lo hi : FlQ) : Verdict :=
  if FlQ.ble K.lo lo && FlQ.ble hi K.hi then .holds else .fails

def ofBool (b : Bool) : Verdict := if b then .holds else .fails

/-- The instances of `Rnd.Sound` at a call of `op` with arguments `a` and result `r`. Each has a
name (the field) and a verdict. -/
def check (op : Nat) (a : Array FlQ) (r : FlQ × FlQ) : List (String × Verdict) :=
  let I : IvQ := ⟨a[0]!, a[1]!⟩
  let J : IvQ := ⟨a[2]!, a[3]!⟩
  let K : IvQ := ⟨r.1, r.2⟩
  let x := a[0]!
  let y := a[1]!
  let z := r.1
  match op with
  | 0 =>
    let mem := if nonempty I && nonempty J then
        bounds K (eadd I.lo J.lo) (eadd I.hi J.hi) else .vacuous
    let lo := match I.lo, J.lo with
      | .top, _ | .nan, _ | _, .top | _, .nan => .vacuous
      | p, q => ofBool (FlQ.ble K.lo (eadd p q))
    [("add", mem), ("add_lo", lo)]
  | 1 =>
    [("sub", if nonempty I && nonempty J then
        bounds K (eadd I.lo (eneg J.hi)) (eadd I.hi (eneg J.lo)) else .vacuous)]
  | 2 =>
    [("mul", if nonempty I && nonempty J then
        let (lo, hi) := corners emul I J
        bounds K lo hi else .vacuous)]
  | 3 =>
    if !(nonempty I && nonempty J) then [("div", .vacuous)]
    else if FlQ.blt (.fin 0) J.lo || FlQ.blt J.hi (.fin 0) then
      let (lo, hi) := corners ediv I J
      [("div", bounds K lo hi)]
    else if J.lo == .fin 0 && J.hi == .fin 0 then [("div", .vacuous)]
    else if K.lo == .bot && K.hi == .top then [("div", .holds)]
    else [("div", .unchecked)]
  | 10 =>
    [("addDn", match x, y with
      | .top, _ | .nan, _ | _, .top | _, .nan => .vacuous
      | p, q => ofBool (FlQ.ble z (eadd p q)))]
  | 11 =>
    [("addUp", match x, y with
      | .bot, _ | .nan, _ | _, .bot | _, .nan => .vacuous
      | p, q => ofBool (FlQ.ble (eadd p q) z))]
  | 12 =>
    let main := match x, y with
      | .top, _ | .nan, _ | _, .bot | _, .nan => .vacuous
      | p, q => ofBool (FlQ.ble z (eadd p (eneg q)))
    let extra := (if x == .bot && y == .bot then [("subDn_ninf", ofBool (z == .nan))] else []) ++
      (if y == .nan then [("subDn_nan", ofBool (z == .nan))] else [])
    ("subDn", main) :: extra
  | 13 =>
    let main := match x, y with
      | .bot, _ | .nan, _ | _, .top | _, .nan => .vacuous
      | p, q => ofBool (FlQ.ble (eadd p (eneg q)) z)
    let extra := (if x == .top && y == .top then [("subUp_inf", ofBool (z == .nan))] else []) ++
      (if y == .nan then [("subUp_nan", ofBool (z == .nan))] else [])
    ("subUp", main) :: extra
  | 14 =>
    [("mulDn", match x, y with
      | .fin p, .fin q => ofBool (FlQ.ble z (.fin (p * q)))
      | _, _ => .vacuous)]
  | 15 =>
    [("mulUp", match x, y with
      | .fin p, .fin q => ofBool (FlQ.ble (.fin (p * q)) z)
      | _, _ => .vacuous)]
  | 16 =>
    [("divDn", match x, y with
      | .fin p, .fin q => if q == 0 then .vacuous else ofBool (FlQ.ble z (.fin (p / q)))
      | _, _ => .vacuous)]
  | 17 =>
    [("divUp", match x, y with
      | .fin p, .fin q => if q == 0 then .vacuous else ofBool (FlQ.ble (.fin (p / q)) z)
      | _, _ => .vacuous)]
  | _ => []

structure Tally where
  calls : Nat := 0
  holds : Nat := 0
  vacuous : Nat := 0
  fails : Nat := 0
  unchecked : Nat := 0

def bump (t : Tally) : Verdict → Tally
  | .holds => { t with holds := t.holds + 1 }
  | .vacuous => { t with vacuous := t.vacuous + 1 }
  | .fails => { t with fails := t.fails + 1 }
  | .unchecked => { t with unchecked := t.unchecked + 1 }

def fields : List String :=
  ["add", "add_lo", "sub", "mul", "div", "addDn", "addUp", "subDn", "subUp", "subDn_ninf",
    "subUp_inf", "subDn_nan", "subUp_nan", "mulDn", "mulUp", "divDn", "divUp"]

def words (s : String) : Array String :=
  ((s.splitOn " ").filter (· != "")).toArray

partial def loop (inp out : IO.FS.Stream) (case : String) (tal : Std.HashMap String Tally)
    (other : Nat) : IO (Std.HashMap String Tally × Nat) := do
  let line ← inp.getLine
  if line.isEmpty then return (tal, other)
  let line := line.trimAsciiEnd.toString
  let w := words line
  match w[0]? with
  | some "C" => loop inp out s!"{w[1]!} {w[2]!}" tal other
  | some "O" =>
    let op := w[1]!.toNat!
    let a := #[ofHex w[2]!, ofHex w[3]!, ofHex w[4]!, ofHex w[5]!]
    let r := (ofHex w[6]!, ofHex w[7]!)
    let vs := check op a r
    if vs.isEmpty then loop inp out case tal (other + 1) else
    let mut tal := tal
    for (f, v) in vs do
      let t := tal.getD f {}
      tal := tal.insert f (bump { t with calls := t.calls + 1 } v)
      if v == .fails then out.putStrLn s!"FAIL {f} {case} {line}"
      if v == .unchecked then out.putStrLn s!"UNCHECKED {f} {case} {line}"
    loop inp out case tal other
  | _ => loop inp out case tal other

end DiffTest

open DiffTest in
def main : IO UInt32 := do
  let out ← IO.getStdout
  let (tal, other) ← loop (← IO.getStdin) out "" {} 0
  out.putStrLn "# field instances checked calls holds vacuous fails unchecked"
  let mut fails := 0
  for f in fields do
    let t := tal.getD f {}
    fails := fails + t.fails
    out.putStrLn s!"F {f} {t.calls} {t.holds} {t.vacuous} {t.fails} {t.unchecked}"
  out.putStrLn s!"NOTCHECKED transcendental calls {other}"
  out.putStrLn s!"FAILS {fails}"
  return 0
