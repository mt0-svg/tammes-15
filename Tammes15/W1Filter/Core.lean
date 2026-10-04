namespace Tammes15.W1Filter

def degGo (b : ByteArray) (n : Nat) : Nat → Nat → Nat → Nat → Bool → Option (Nat × Bool)
  | 0, _, _, _, _ => none
  | fuel + 1, i, v, c, ok =>
    if n ≤ v then some (i, ok)
    else if h : i < b.size then
      if (b[i]'h).toNat = 0 then degGo b n fuel (i + 1) (v + 1) 0 (ok && 3 ≤ c && c ≤ 5)
      else degGo b n fuel (i + 1) v (c + 1) ok
    else none

def degPass (b : ByteArray) (o : Nat) : Option (Nat × Bool) :=
  if h : o < b.size then
    let n := (b[o]'h).toNat
    if n = 0 then none else degGo b n (b.size - o) (o + 1) 0 0 true
  else none

structure Darts where
  n : Nat
  fst : Array Nat
  snd : Array Nat
  off : Array Nat
  deriving Repr

def scan (b : ByteArray) (n : Nat) :
    Nat → Nat → Nat → Array Nat → Array Nat → Array Nat →
      Option (Nat × Array Nat × Array Nat × Array Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, i, v, fst, snd, off =>
    if n ≤ v then some (i, fst, snd, off)
    else if h : i < b.size then
      let x := (b[i]'h).toNat
      if x = 0 then scan b n fuel (i + 1) (v + 1) fst snd (off.push fst.size)
      else scan b n fuel (i + 1) v (fst.push v) (snd.push (x - 1)) off
    else none

def decode (b : ByteArray) (o : Nat) : Option (Nat × Darts) :=
  if h : o < b.size then
    let n := (b[o]'h).toNat
    if n = 0 then none
    else
      match scan b n (b.size - o) (o + 1) 0 #[] #[] #[0] with
      | none => none
      | some (e, fst, snd, off) => some (e, ⟨n, fst, snd, off⟩)
  else none

def Darts.D (g : Darts) : Nat := g.fst.size

def Darts.deg (g : Darts) (v : Nat) : Nat := g.off.getD (v + 1) 0 - g.off.getD v 0

def allFrom (P : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | len + 1, i => P i && allFrom P len (i + 1)

def posGo (g : Darts) : Nat → Nat → Array Nat → Option (Array Nat)
  | 0, _, t => some t
  | len + 1, k, t =>
    let v := g.fst.getD k 0
    let w := g.snd.getD k 0
    let j := v * g.n + w
    if w < g.n && w != v && t.getD j 0 == 0 then posGo g len (k + 1) (t.set! j (k + 1))
    else none

def Darts.posTable (g : Darts) : Option (Array Nat) :=
  posGo g g.D 0 (Array.replicate (g.n * g.n) 0)

def faceGo (g : Darts) (t : Array Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, acc => acc
  | len + 1, k, acc =>
    let v := g.fst.getD k 0
    let w := g.snd.getD k 0
    let r := t.getD (w * g.n + v) 0 - 1
    let o := g.off.getD w 0
    let d := g.deg w
    faceGo g t len (k + 1) (acc.push (o + (r - o + d - 1) % d))

def Darts.validT (g : Darts) (t : Array Nat) : Bool :=
  g.off.size == g.n + 1 && g.snd.size == g.D && g.off.getD g.n 0 == g.D &&
    allFrom (fun k => t.getD (g.snd.getD k 0 * g.n + g.fst.getD k 0) 0 != 0) g.D 0

def Darts.tableFaces (g : Darts) : Option (Array Nat) :=
  match g.posTable with
  | none => none
  | some t => if g.validT t then some (faceGo g t g.D 0 (Array.mkEmpty g.D)) else none

def periodGoA (fa : Array Nat) (i : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, cur, t =>
    let nx := fa.getD cur 0
    if nx = i then t else periodGoA fa i fuel nx (t + 1)

def countBlock (fa : Array Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, _, t, q, p => (t, q, p)
  | len + 1, k, t, q, p =>
    let s := periodGoA fa k 6 k 1
    if s = 3 then countBlock fa len (k + 1) (t + 1) q p
    else if s = 4 then countBlock fa len (k + 1) t (q + 1) p
    else countBlock fa len (k + 1) t q (p + 1)

def w1Type (t q p : Nat) : Bool :=
  t + q + p ≤ 5 && (2 ≤ p || (p == 1 && 3 ≤ t + 2 * q) || (p == 0 && 6 ≤ t + 2 * q))

def Darts.w1Blocks (g : Darts) (fa : Array Nat) : Bool :=
  allFrom (fun v =>
    let (a, q, p) := countBlock fa (g.deg v) (g.off.getD v 0) 0 0 0
    w1Type a q p) g.n 0

def Darts.none : Darts := ⟨0, #[], #[], #[]⟩

def filterRec (b : ByteArray) (o : Nat) : Option (Nat × Bool × Darts × Array Nat) :=
  match degPass b o with
  | none => none
  | some (e, false) => some (e, false, Darts.none, #[])
  | some (_, true) =>
    match decode b o with
    | none => none
    | some (e, g) =>
      match g.tableFaces with
      | none => none
      | some fa => some (e, g.w1Blocks fa, g, fa)

def packBytes (a : Array Nat) : Nat :=
  a.foldr (fun x acc => acc * 256 + x % 256) 0

structure GC where
  D : Nat
  face : Nat
  fst : Nat
  deriving Repr, DecidableEq

def gcOf (g : Darts) (fa : Array Nat) : GC := ⟨g.D, packBytes fa, packBytes g.fst⟩

def le4 (x : Nat) : ByteArray :=
  ⟨#[(x % 256).toUInt8, (x / 256 % 256).toUInt8, (x / 65536 % 256).toUInt8,
    (x / 16777216 % 256).toUInt8]⟩

def natBytes : Nat → Nat → ByteArray
  | _, 0 => ByteArray.empty
  | x, k + 1 => ⟨#[(x % 256).toUInt8]⟩ ++ natBytes (x / 256) k

def gcBytes (c : GC) : ByteArray :=
  le4 1 ++ natBytes c.D 1 ++ le4 c.D ++ natBytes c.face c.D ++ le4 c.D ++ natBytes c.fst c.D

def GC.inRange (c : GC) : Bool := c.D < 256 && c.face < 256 ^ c.D && c.fst < 256 ^ c.D

end Tammes15.W1Filter
