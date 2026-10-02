import Mathlib

/-!
# The arithmetic of the program (Definition 5.5 (1) of the paper)

The first program (code/impl1/rust/src) computes in binary64 with outward rounding. This module
fixes how its values and its interval operations are read in Lean, and what is assumed of them.

* `Fl`: a binary64 value, read as an extended real (the two zeros are one value), or NaN. The order
  `Fl.le`, `Fl.lt` is IEEE's (false when either side is NaN), `Fl.max`, `Fl.min` are `f64::max`,
  `f64::min` (the other argument when one is NaN).
* `Iv`: an interval of ivt.rs (`Iv`), two float ends; `Iv.Mem I x` is `Iv::contains`.
* `Rnd`: the arithmetic the contractors call, as functions: the interval operations of ivt.rs
  (`add`, `sub`, `mul`, `div`, `cos`, `sin`, `acos`, `asin`, `atan`, `tan`), the directed point
  operations of iv.rs (`add_dn`, `add_up`, `sub_dn`, `sub_up`, `mul_dn`, `mul_up`, `div_dn`,
  `div_up`) and the constants `PI_LO`, `PI_HI`, `TWO_PI_LO`, `TWO_PI_HI` of iv.rs.
* `Rnd.Sound`: what is assumed of them, and nothing else: each interval operation contains the exact
  value at every point of its inputs (inside the domain of the function), each point operation
  rounds in its direction (also at infinite ends, and NaN where IEEE gives NaN), and the constants
  enclose `π` and `2π`. This is the whole computational content left outside Lean by the soundness
  of the contractors: no statement of this module mentions a geometric object.

The arithmetic claim left outside Lean, (i) of Sections 5.5 and 10.8 of the paper: the operations of
the program, extended to every value of `Fl` as Lean reads them (NaN and infinite ends included),
form an `R : Rnd` with `R.Sound`. The procedures `N` of `Contractors.Impl N` (Statement.lean) are
the program on boxes whose ends are floats, and on the other boxes the identity: the narrowing
returns the box (the run that stops at once) and the wheel gives no enclosure.

The contractors themselves (`Tammes15.Contractors.Prims`) are written over an arbitrary `R : Rnd`,
line for line as the Rust code, and their soundness is proved for every `R` with `R.Sound`.
-/

namespace Tammes15.Contractors

open Real

/-- A binary64 value of the program: an extended real (finite or infinite; the two zeros are one
value), or NaN. -/
inductive Fl
  | num (x : EReal)
  | nan

namespace Fl

/-- IEEE `a ≤ b`: false when either side is NaN. -/
def le : Fl → Fl → Prop
  | num a, num b => a ≤ b
  | _, _ => False

/-- IEEE `a < b`: false when either side is NaN. -/
def lt : Fl → Fl → Prop
  | num a, num b => a < b
  | _, _ => False

/-- `f64::max`: the other argument when one is NaN. -/
noncomputable def max : Fl → Fl → Fl
  | nan, b => b
  | num a, nan => num a
  | num a, num b => num (Max.max a b)

/-- `f64::min`: the other argument when one is NaN. -/
noncomputable def min : Fl → Fl → Fl
  | nan, b => b
  | num a, nan => num a
  | num a, num b => num (Min.min a b)

/-- `f64::is_finite`. -/
def IsFinite : Fl → Prop
  | num a => a ≠ ⊤ ∧ a ≠ ⊥
  | nan => False

/-- The real value of a finite float (`0` for the others, which are never read so). -/
noncomputable def toReal : Fl → ℝ
  | num a => a.toReal
  | nan => 0

/-- A real number as a float value. -/
noncomputable def ofReal (x : ℝ) : Fl := num (x : EReal)

/-- `f64::INFINITY`. -/
noncomputable def inf : Fl := num ⊤

/-- `f64::NEG_INFINITY`. -/
noncomputable def ninf : Fl := num ⊥

end Fl

/-- An interval of the program (ivt.rs `Iv`): two float ends. -/
structure Iv where
  lo : Fl
  hi : Fl

namespace Iv

/-- `Iv::contains`: the real `x` lies between the ends (never when an end is NaN). -/
def Mem (I : Iv) (x : ℝ) : Prop :=
  Fl.le I.lo (Fl.ofReal x) ∧ Fl.le (Fl.ofReal x) I.hi

/-- `Iv::pt`. -/
def pt (x : Fl) : Iv := ⟨x, x⟩

/-- The interval of two real ends. -/
noncomputable def ofReal (lo hi : ℝ) : Iv := ⟨Fl.ofReal lo, Fl.ofReal hi⟩

/-- `usable` (deep.rs): no NaN end and `lo ≤ hi`. -/
def Usable (I : Iv) : Prop := Fl.le I.lo I.hi

/-- `Iv::meet`. -/
noncomputable def meet (I J : Iv) : Iv := ⟨Fl.max I.lo J.lo, Fl.min I.hi J.hi⟩

end Iv

/-- The arithmetic of the program: the interval operations of ivt.rs, the directed point operations
of iv.rs and the constants of iv.rs, as functions. -/
structure Rnd where
  /-- `Iv::add` -/
  add : Iv → Iv → Iv
  /-- `Iv::sub` -/
  sub : Iv → Iv → Iv
  /-- `Iv::mul` (and `Iv::scale c`, which is `mul (pt c)`) -/
  mul : Iv → Iv → Iv
  /-- `Iv::div` -/
  div : Iv → Iv → Iv
  /-- `Iv::cos` -/
  cos : Iv → Iv
  /-- `Iv::sin` -/
  sin : Iv → Iv
  /-- `Iv::acos` -/
  acos : Iv → Iv
  /-- `Iv::asin` -/
  asin : Iv → Iv
  /-- `Iv::atan` -/
  atan : Iv → Iv
  /-- `Iv::tan` -/
  tan : Iv → Iv
  /-- iv.rs `add_dn` -/
  addDn : Fl → Fl → Fl
  /-- iv.rs `add_up`, and `(a + b).next_up()` -/
  addUp : Fl → Fl → Fl
  /-- iv.rs `sub_dn` -/
  subDn : Fl → Fl → Fl
  /-- iv.rs `sub_up` -/
  subUp : Fl → Fl → Fl
  /-- iv.rs `mul_dn` -/
  mulDn : Fl → Fl → Fl
  /-- iv.rs `mul_up` -/
  mulUp : Fl → Fl → Fl
  /-- iv.rs `div_dn` -/
  divDn : Fl → Fl → Fl
  /-- iv.rs `div_up` -/
  divUp : Fl → Fl → Fl
  /-- iv.rs `PI_LO` -/
  piLo : ℝ
  /-- iv.rs `PI_HI` -/
  piHi : ℝ
  /-- iv.rs `TWO_PI_LO` -/
  twoPiLo : ℝ
  /-- iv.rs `TWO_PI_HI` -/
  twoPiHi : ℝ

/-- What is assumed of the arithmetic of the program: outward rounding. Interval operations contain
the exact value at every point of their inputs (inside the domain of the function, and away from a
zero divisor); point operations round in their direction, read with lower or upper bounds of their
arguments (so that infinite ends are covered), give NaN where IEEE does (`-∞ - -∞`, `∞ - ∞`, a NaN
argument), and the constants enclose `π` and `2π`. The lower end of a sum is also a lower bound
from lower bounds of the summands alone (ivt.rs `add`: `(lo + lo).next_down()`), which covers an
infinite end. -/
structure Rnd.Sound (R : Rnd) : Prop where
  add : ∀ I J x y, I.Mem x → J.Mem y → (R.add I J).Mem (x + y)
  add_lo : ∀ I J (x y : ℝ), Fl.le I.lo (.ofReal x) → Fl.le J.lo (.ofReal y) →
    Fl.le (R.add I J).lo (.ofReal (x + y))
  sub : ∀ I J x y, I.Mem x → J.Mem y → (R.sub I J).Mem (x - y)
  mul : ∀ I J x y, I.Mem x → J.Mem y → (R.mul I J).Mem (x * y)
  div : ∀ I J x y, I.Mem x → J.Mem y → y ≠ 0 → (R.div I J).Mem (x / y)
  cos : ∀ I x, I.Mem x → (R.cos I).Mem (Real.cos x)
  sin : ∀ I x, I.Mem x → (R.sin I).Mem (Real.sin x)
  acos : ∀ I x, I.Mem x → -1 ≤ x → x ≤ 1 → (R.acos I).Mem (Real.arccos x)
  asin : ∀ I x, I.Mem x → -1 ≤ x → x ≤ 1 → (R.asin I).Mem (Real.arcsin x)
  atan : ∀ I x, I.Mem x → (R.atan I).Mem (Real.arctan x)
  tan : ∀ I x, I.Mem x → -(π / 2) < x → x < π / 2 → (R.tan I).Mem (Real.tan x)
  addDn : ∀ a b (x y : ℝ), Fl.le a (.ofReal x) → Fl.le b (.ofReal y) →
    Fl.le (R.addDn a b) (.ofReal (x + y))
  addUp : ∀ a b (x y : ℝ), Fl.le (.ofReal x) a → Fl.le (.ofReal y) b →
    Fl.le (.ofReal (x + y)) (R.addUp a b)
  subDn : ∀ a b (x y : ℝ), Fl.le a (.ofReal x) → Fl.le (.ofReal y) b →
    Fl.le (R.subDn a b) (.ofReal (x - y))
  subUp : ∀ a b (x y : ℝ), Fl.le (.ofReal x) a → Fl.le b (.ofReal y) →
    Fl.le (.ofReal (x - y)) (R.subUp a b)
  subDn_ninf : R.subDn Fl.ninf Fl.ninf = .nan
  subUp_inf : R.subUp Fl.inf Fl.inf = .nan
  subDn_nan : ∀ a, R.subDn a .nan = .nan
  subUp_nan : ∀ a, R.subUp a .nan = .nan
  mulDn : ∀ x y : ℝ, Fl.le (R.mulDn (.ofReal x) (.ofReal y)) (.ofReal (x * y))
  mulUp : ∀ x y : ℝ, Fl.le (.ofReal (x * y)) (R.mulUp (.ofReal x) (.ofReal y))
  divDn : ∀ x y : ℝ, y ≠ 0 → Fl.le (R.divDn (.ofReal x) (.ofReal y)) (.ofReal (x / y))
  divUp : ∀ x y : ℝ, y ≠ 0 → Fl.le (.ofReal (x / y)) (R.divUp (.ofReal x) (.ofReal y))
  piLo : R.piLo ≤ π
  piHi : π ≤ R.piHi
  twoPiLo : R.twoPiLo ≤ 2 * π
  twoPiHi : 2 * π ≤ R.twoPiHi

end Tammes15.Contractors
