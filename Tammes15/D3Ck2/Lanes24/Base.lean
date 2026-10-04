namespace Lanes24

def ONE : Nat := 16777216
def PI24 : Nat := 52707179
def HPI24 : Nat := 26353589
def QPI24 : Nat := 13176794
def HALF : Nat := 8388608
def C6 : Nat := 2796203
def C24 : Nat := 699051
def C120 : Nat := 139810
def C720 : Nat := 23302
def C5040 : Nat := 3329
def C40320 : Nat := 416
def C362880 : Nat := 46

@[inline] def fm (a b : Nat) : Nat := Nat.shiftRight (Nat.mul a b) 24

@[inline] def lt (a b : Nat) : Nat := if Nat.blt a b then 1 else 0

def fld (n : Nat) (i : Nat) : Nat := Nat.mod (Nat.shiftRight n (Nat.add 64 (Nat.mul 56 i))) 72057594037927936

def fld24 (n : Nat) (i : Nat) : Nat := Nat.shiftRight (Nat.add (fld n i) 33554432) 26

@[inline] def mH (O : Nat) : Nat := Nat.mul O 9223372036854775808

@[inline] def m63 (O : Nat) : Nat := Nat.mul O 9223372036854775807

@[inline] def rep (O v : Nat) : Nat := Nat.mul O v

@[inline] def pmask (b : Nat) : Nat := Nat.mul b 9223372036854775807

@[inline] def psub (O x y : Nat) : Nat :=
  let D := Nat.sub (Nat.add x (mH O)) y
  Nat.land D (pmask (Nat.shiftRight (Nat.land D (mH O)) 63))

@[inline] def plt (O x y : Nat) : Nat :=
  Nat.shiftRight (Nat.land (Nat.sub (Nat.add y (mH O)) (Nat.add x O)) (mH O)) 63

@[inline] def pshr1 (O x : Nat) : Nat := Nat.land (Nat.shiftRight x 1) (m63 O)
@[inline] def pshr3 (O x : Nat) : Nat := Nat.land (Nat.shiftRight x 3) (Nat.mul O 2305843009213693951)

@[inline] def psel (M A B : Nat) : Nat := Nat.xor B (Nat.land (Nat.xor A B) M)

def lamA (K : Nat) (O A B : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × Nat) (0, 0)
    (fun _ p => (Nat.add p.1 (Nat.land (Nat.shiftLeft A p.2)
      (Nat.mul (Nat.land (Nat.shiftRight B p.2) O) 18446744073709551615)), Nat.add p.2 1)) K).1

noncomputable def cnd {α : Type} (b : Bool) (x y : α) : α :=
  @Bool.rec (fun _ => α) y x b

noncomputable def frc2 {α : Type} (a b : Nat) (k : Nat → Nat → α) : α :=
  cnd (Nat.beq a 0) (cnd (Nat.beq b 0) (k 0 0) (k 0 b)) (cnd (Nat.beq b 0) (k a 0) (k a b))

noncomputable def mulBit2 (A k P : Nat) (ih : Nat → Nat) (bt : Nat) : Nat :=
  frc2 (Nat.add P (Nat.land (Nat.shiftLeft A k) (Nat.sub (Nat.shiftLeft bt 64) bt))) 1 (fun P _ => ih P)

noncomputable def mulBit (O A B k P : Nat) (ih : Nat → Nat) : Nat :=
  mulBit2 A k P ih (Nat.land (Nat.shiftRight B k) O)

noncomputable def mulR (K : Nat) (O A B : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun P => P) (fun k ih P => mulBit O A B k P ih) K 0

def laneAt (x i : Nat) : Nat := Nat.mod (Nat.shiftRight x (Nat.mul 64 i)) 18446744073709551616

end Lanes24
