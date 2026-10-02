import Tammes15.Contractors.DiffTest.PrimsQ

/-!
# Floats of the stream of the differential test (Section 10.4 of the paper)

The bits of a double read as an exact value (`ofBits`), and written back (`tok`): the bits when the
value is a double, `q<num>/<den>` otherwise.
-/

open Tammes15.Contractors.Q

namespace DiffTest

def hexVal (c : Char) : UInt64 :=
  if c.isDigit then (c.toNat - 48).toUInt64 else (c.toNat - 87).toUInt64

def parseHex (s : String) : UInt64 :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

/-- The value of the double with bits `b`. -/
def ofBits (b : UInt64) : FlQ :=
  let neg := (b >>> 63) == 1
  let e := ((b >>> 52) &&& 0x7ff).toNat
  let m := (b &&& 0xfffffffffffff).toNat
  if e == 0x7ff then
    if m == 0 then (if neg then .bot else .top) else .nan
  else
    let mant : Nat := if e == 0 then m else m + 2 ^ 52
    let ex : Int := if e == 0 then -1074 else (e : Int) - 1075
    let mag : Rat :=
      if 0 ≤ ex then ((mant * 2 ^ ex.toNat : Nat) : Rat) else mkRat mant (2 ^ (-ex).toNat)
    .fin (if neg then -mag else mag)

def ofHex (s : String) : FlQ := ofBits (parseHex s)

/-- The number of trailing zero bits of `n > 0`. -/
def tz (n : Nat) : Nat := Id.run do
  let mut k := 0
  let mut m := n
  for _ in [0:2200] do
    if m % 2 == 0 && m != 0 then
      m := m / 2
      k := k + 1
  return k

/-- The bits of the double equal to `q`, when there is one. -/
def ratBits? (q : Rat) : Option UInt64 :=
  if q == 0 then some 0 else
  let neg := q.num < 0
  let d := q.den
  if d &&& (d - 1) != 0 then none else
  let n0 := q.num.natAbs
  let t := tz n0
  let n := n0 >>> t
  -- q = ± n * 2 ^ (t - k), n odd
  let k : Int := (Nat.log2 d : Int) - t
  let L := Nat.log2 n + 1
  let E : Int := (L : Int) - 1 - k
  let sign : UInt64 := if neg then (1 : UInt64) <<< 63 else 0
  if E > 1023 then none
  else if E ≥ -1022 then
    if L ≤ 53 then
      let M := n * 2 ^ (53 - L)
      some (sign ||| ((E + 1023).toNat.toUInt64 <<< 52) ||| (M - 2 ^ 52).toUInt64)
    else none
  else
    if k ≤ 1074 then some (sign ||| (n * 2 ^ (1074 - k).toNat).toUInt64) else none

def hex16 (b : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- A float as a token of the stream. -/
def tok : FlQ → String
  | .fin q => match ratBits? q with
    | some b => hex16 b
    | none => s!"q{q.num}/{q.den}"
  | .top => "7ff0000000000000"
  | .bot => "fff0000000000000"
  | .nan => "7ff8000000000000"

instance : Hashable FlQ where
  hash
    | .fin q => mixHash (hash q.num) (hash q.den)
    | .top => 11
    | .bot => 13
    | .nan => 17

end DiffTest
