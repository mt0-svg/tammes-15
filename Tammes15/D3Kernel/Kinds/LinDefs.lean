import Tammes15.D3Kernel.Kinds.Keys

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Pent

def ntab (g : ℕ) : ℕ := bits g 5184 8

def ent (g j : ℕ) : ℕ := bits g (5248 + 128 * j) 128

def eNt (E : ℕ) : ℕ := bits E 0 3

def eCc (E : ℕ) : ℕ := bits E 3 2

def eTs (E : ℕ) : ℕ := E / 2 ^ 8

def tVar (Ts q : ℕ) : ℕ := bits Ts (10 * q) 6

def tNeg (Ts q : ℕ) : ℕ := bits Ts (10 * q + 6) 1

def tMag (Ts q : ℕ) : ℕ := bits Ts (10 * q + 7) 3

def eFam (E : ℕ) : ℕ := bits E 64 3

def eX (E : ℕ) : ℕ := bits E 67 8

def eO (E : ℕ) : ℕ := bits E 75 8

def eE (E : ℕ) : ℕ := bits E 83 8

def eTau (E i : ℕ) : ℕ := bits E (91 + 3 * i) 3

def cTPH : ℕ := 28976077832308491370

def cTPL : ℕ := 28976077832308491369

def cSHI : ℕ := 17209430578547353542

def bP (cc : ℕ) : ℕ :=
  @Bool.rec (fun _ => ℕ) (@Bool.rec (fun _ => ℕ) 0 cSHI (Nat.beq cc 3)) cTPH (Nat.beq cc 1)

def bN (cc : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 0 cTPL (Nat.beq cc 2)

noncomputable def tCoef (Ts q : ℕ) : ℝ := if tNeg Ts q = 1 then -(tMag Ts q : ℝ) else (tMag Ts q : ℝ)

noncomputable def rowSum (E : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.range (eNt E), tCoef (eTs E) q * x (tVar (eTs E) q)

noncomputable def rowRhs (E : ℕ) : ℝ := ((bP (eCc E) : ℝ) - (bN (eCc E) : ℝ)) / 2 ^ 62

def RowValid (g E : ℕ) : Prop :=
  (∀ q < eNt E, tVar (eTs E) q < Ctx.nv g) ∧ ∀ s : Sol g, rowSum E s.x ≤ rowRhs E

def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

def countBelow (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => countBelow p n + if p n then 1 else 0

def dvOK (g w i : ℕ) : Bool :=
  Nat.blt w (Ctx.nv g) && Nat.blt i (Ctx.code g).D &&
    (Nat.beq (Ctx.mean g w) (2 + i) ||
      (Nat.beq (Ctx.mean g w) 0 && Nat.beq ((Ctx.code g).period i) 3) ||
      (Nat.beq (Ctx.mean g w) (2 + (Ctx.code g).faceIter i 2) && Nat.beq ((Ctx.code g).period i) 4))

def aOK (g w : ℕ) : Bool := Nat.blt w (Ctx.nv g) && Nat.beq (Ctx.mean g w) 0

def tIs (Ts q ng mg : ℕ) : Bool := Nat.beq (tNeg Ts q) ng && Nat.beq (tMag Ts q) mg

def fstSorted (c : GCode) : Bool := allBelow (fun i => Nat.ble (c.fstAt i) (c.fstAt (i + 1))) (c.D - 1)

def vertOK (g E ng : ℕ) : Bool :=
  let c := Ctx.code g
  let v := eX E
  let o := eO E
  let e := eE E
  let Ts := eTs E
  Nat.ble (eNt E) 5 && Nat.blt o e && Nat.ble e c.D && Nat.ble e (o + 5) &&
    (Nat.beq o 0 || Nat.blt (c.fstAt (o - 1)) v) && (Nat.beq e c.D || Nat.blt v (c.fstAt e)) &&
    allBelow (fun i => Nat.beq (c.fstAt (o + i)) v && Nat.blt (eTau E i) (eNt E) &&
      dvOK g (tVar Ts (eTau E i)) (o + i) && Nat.beq (tNeg Ts (eTau E i)) ng) (e - o) &&
    allBelow (fun q => Nat.blt (tVar Ts q) (Ctx.nv g) &&
      Nat.beq (tMag Ts q) (countBelow (fun i => Nat.beq (eTau E i) q) (e - o))) (eNt E)

def entOK (g E : ℕ) : Bool :=
  let c := Ctx.code g
  let i := eX E
  let Ts := eTs E
  let f := eFam E
  @Bool.rec (fun _ => Bool)
    (@Bool.rec (fun _ => Bool)
      (@Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          (@Bool.rec (fun _ => Bool)
            (Nat.beq f 5 && Nat.beq (eCc E) 2 && vertOK g E 1)
            (Nat.beq (eCc E) 1 && vertOK g E 0) (Nat.beq f 4))
          (Nat.beq (eNt E) 2 && Nat.beq (eCc E) 3 && Nat.beq (c.period i) 4 &&
            tIs Ts 0 0 1 && dvOK g (tVar Ts 0) i && tIs Ts 1 0 1 && dvOK g (tVar Ts 1) (c.faceAt i))
          (Nat.beq f 3))
        (Nat.beq (eNt E) 3 && Nat.beq (eCc E) 0 && Nat.beq (c.period i) 4 &&
          tIs Ts 0 0 3 && aOK g (tVar Ts 0) && tIs Ts 1 1 1 && dvOK g (tVar Ts 1) i &&
          tIs Ts 2 1 1 && dvOK g (tVar Ts 2) (c.faceAt i))
        (Nat.beq f 2))
      (Nat.beq (eNt E) 2 && Nat.beq (eCc E) 0 && Nat.beq (c.period i) 4 &&
        tIs Ts 0 0 1 && dvOK g (tVar Ts 0) i && tIs Ts 1 1 2 && aOK g (tVar Ts 1))
      (Nat.beq f 1))
    (Nat.beq (eNt E) 2 && Nat.beq (eCc E) 0 &&
      tIs Ts 0 0 1 && aOK g (tVar Ts 0) && tIs Ts 1 1 1 && dvOK g (tVar Ts 1) i)
    (Nat.beq f 0)

def validCtx (g : ℕ) : Bool :=
  fstSorted (Ctx.code g) && allBelow (fun j => entOK g (ent g j)) (ntab g)

def ntabK (g : ℕ) : ℕ := Nat.land (Nat.shiftRight g (nat_lit 5184)) (nat_lit 255)

def entK (g j : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight g (Nat.add (nat_lit 5248) (Nat.shiftLeft j (nat_lit 7))))
    (nat_lit 340282366920938463463374607431768211455)

def linAcc (box v : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool) (n : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → Bool)
    (fun _ cp cn P Q => k cp cn P Q)
    (fun _ ih Ts cp cn P Q =>
      let w := Nat.land Ts (nat_lit 63)
      let ng := Nat.land (Nat.shiftRight Ts (nat_lit 6)) (nat_lit 1)
      let mg := Nat.land (Nat.shiftRight Ts (nat_lit 7)) (nat_lit 7)
      let Ts' := Nat.shiftRight Ts (nat_lit 10)
      let key := bk box (Nat.add (Nat.shiftLeft w (nat_lit 1)) ng)
      @Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool) false
            (@Bool.rec (fun _ => Bool) (ih Ts' cp cn P (Nat.add Q (Nat.mul mg (kfix key))))
              (ih Ts' cp cn (Nat.add P (Nat.mul mg (kfix key))) Q) (Nat.beq ng (nat_lit 0)))
            (kgood key))
        (@Bool.rec (fun _ => Bool) (ih Ts' cp (Nat.add cn mg) P Q) (ih Ts' (Nat.add cp mg) cn P Q)
          (Nat.beq ng (nat_lit 0)))
        (Nat.beq w v))
    n

def recFin (side nf cc : ℕ) (cp cn P Q : ℕ) : Bool :=
  @Bool.rec (fun _ => Bool)
    (Nat.beq cp 0 && Nat.blt 0 cn &&
      Nat.ble (Nat.add (Nat.add (Nat.mul cn nf) Q) (bP cc)) (Nat.add P (bN cc)))
    (Nat.beq cn 0 && Nat.blt 0 cp &&
      Nat.ble (Nat.add Q (bP cc)) (Nat.add (Nat.add (Nat.mul cp nf) P) (bN cc)))
    (Nat.beq side 1)

def emptyFin (cc : ℕ) (_ _ P Q : ℕ) : Bool := Nat.blt (Nat.add Q (bP cc)) (Nat.add P (bN cc))

def linRec (g box it : ℕ) : Bool :=
  let j := fk it 75 127
  let E := entK g j
  let t := fk it 64 127
  let n := Nat.land it (nat_lit 18446744073709551615)
  let cc := Nat.land (Nat.shiftRight E (nat_lit 3)) (nat_lit 3)
  let nt := Nat.land E (nat_lit 7)
  let Ts := Nat.shiftRight E (nat_lit 8)
  Nat.blt j (ntabK g) &&
    @Bool.rec (fun _ => Bool) (linAcc box 64 (emptyFin cc) nt Ts 0 0 0 0) true
      (kgood n && linAcc box (Nat.shiftRight t (nat_lit 1)) (recFin (Nat.land t (nat_lit 1)) (kfix n) cc) nt Ts
        0 0 0 0)

def linKill (g box it : ℕ) : Bool :=
  let j := fk it 75 127
  let E := entK g j
  let cc := Nat.land (Nat.shiftRight E (nat_lit 3)) (nat_lit 3)
  let nt := Nat.land E (nat_lit 7)
  let Ts := Nat.shiftRight E (nat_lit 8)
  Nat.blt j (ntabK g) && linAcc box 64 (emptyFin cc) nt Ts 0 0 0 0

def ctxOK (g last : ℕ) : Bool := @Bool.rec (fun _ => Bool) (validCtx g) true (Nat.beq (Nat.succ g) last)

def linChecker : Checker where
  σ := Bool × ℕ
  H := Unit
  init := (true, 0)
  onRec g box it s := (s.1 && ctxOK g s.2 && linRec g box it, Nat.succ g)
  onKill g box it s := (s.1 && ctxOK g s.2 && linKill g box it, Nat.succ g)
  fin s _ := s.1
  frc s k := @Bool.rec (fun _ => List ℕ) (k (false, s.2)) (k (true, s.2)) s.1
  frc_eq s k := by obtain ⟨b, n⟩ := s; cases b <;> rfl

end Tammes15.D3Kernel.Kinds
