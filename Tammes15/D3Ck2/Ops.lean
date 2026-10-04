import Tammes15.D3Ck2.Lanes24.MulF

namespace D3Ck2

open Lanes24

noncomputable def cat (l : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0 (fun c _ ih => Nat.lor (Nat.shiftRight c 64) (Nat.shiftLeft ih 4096)) l

noncomputable def oN (n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft n 6)) 1) 18446744073709551615

noncomputable def sabs (O X : Nat) : Nat × Nat :=
  let sg := plt O X (Nat.mul O 4611686018427387904)
  let A := Nat.land (Nat.sub (Nat.add X (mH O)) (Nat.mul O 4611686018427387904)) (m63 O)
  let B := Nat.land (Nat.sub (Nat.mul O 13835058055282163712) X) (m63 O)
  (sg, psel (pmask sg) B A)

noncomputable def smx (K O X Y : Nat) : Nat :=
  let a := sabs O X
  let b := sabs O Y
  let p := mulF K O a.2 b.2
  psel (pmask (Nat.xor a.1 b.1)) (Nat.sub (Nat.mul O 4611686018427387904) p)
    (Nat.add (Nat.mul O 4611686018427387904) p)

noncomputable def srdF (O X : Nat) : Nat :=
  let a := sabs O X
  let mg := Nat.land (Nat.shiftRight (Nat.add a.2 (Nat.mul a.1 268435455)) 28) (Nat.mul O 68719476735)
  psel (pmask a.1) (Nat.sub (Nat.mul O 4611686018427387904) mg) (Nat.add (Nat.mul O 4611686018427387904) mg)

noncomputable def srdC (O X : Nat) : Nat :=
  let a := sabs O X
  let mg := Nat.land (Nat.shiftRight (Nat.add a.2 (Nat.mul (Nat.sub O a.1) 268435455)) 28)
    (Nat.mul O 68719476735)
  psel (pmask a.1) (Nat.sub (Nat.mul O 4611686018427387904) mg) (Nat.add (Nat.mul O 4611686018427387904) mg)

noncomputable def sshl (O X : Nat) : Nat :=
  let a := sabs O X
  let s := Nat.shiftLeft a.2 28
  psel (pmask a.1) (Nat.sub (Nat.mul O 4611686018427387904) s) (Nat.add (Nat.mul O 4611686018427387904) s)

noncomputable def pfm28 (O A B : Nat) : Nat :=
  Nat.land (Nat.shiftRight (mulF 28 O A B) 28) (Nat.mul O 68719476735)

noncomputable def pfmc28 (O A k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul A k) 28) (Nat.mul O 68719476735)

noncomputable def sc28 (O X : Nat) : Nat × Nat :=
  let x0 := Nat.land (Nat.sub (Nat.add X (mH O)) (Nat.mul O 4611686018427387904)) (m63 O)
  let x := psel (pmask (plt O (rep O 843314857) x0)) (rep O 843314857) x0
  let negb := plt O (rep O 421657428) x
  let nm := pmask negb
  let x1 := psel nm (psub O (rep O 843314856) x) x
  let sm := pmask (plt O (rep O 210828714) x1)
  let z := psel sm (Nat.sub (rep O 421657428) x1) x1
  let z2 := pfm28 O z z
  let c := Nat.sub (rep O 268435456) (pfm28 O (Nat.sub (rep O 134217728) (pfm28 O (Nat.sub (rep O 11184811)
    (pfm28 O (Nat.sub (rep O 372827) (pfm28 O (Nat.sub (rep O 6658) (pfmc28 O z2 74)) z2)) z2)) z2)) z2)
  let s := pfm28 O (Nat.sub (rep O 268435456) (pfm28 O (Nat.sub (rep O 44739243) (pfm28 O (Nat.sub
    (rep O 2236962) (pfm28 O (Nat.sub (rep O 53261) (pfmc28 O z2 740)) z2)) z2)) z2)) z
  let sv := psel sm c s
  let cv := psel sm s c
  (Nat.add (Nat.mul O 4611686018427387904) sv,
    psel nm (Nat.sub (Nat.mul O 4611686018427387904) cv) (Nat.add (Nat.mul O 4611686018427387904) cv))

noncomputable def ix (O F s : Nat) : Nat :=
  Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight F s) (Nat.mul O 4294967295)) 4) (Nat.mul O 4611686018427387904)

noncomputable def hxa (O H s : Nat) : Nat :=
  Nat.add (Nat.land (Nat.shiftRight H s) (Nat.mul O 1073741823)) (Nat.mul O 4611686018427387904)

noncomputable def hxs (O H s : Nat) : Nat :=
  Nat.add (Nat.land (Nat.shiftRight H s) (Nat.mul O 4294967295)) (Nat.mul O 4611686016279904256)

noncomputable def red28 (O X : Nat) : Nat × Nat × Nat :=
  let x0 := Nat.land (Nat.sub (Nat.add X (mH O)) (Nat.mul O 4611686018427387904)) (m63 O)
  let x := psel (pmask (plt O (rep O 843314857) x0)) (rep O 843314857) x0
  let negb := plt O (rep O 421657428) x
  let nm := pmask negb
  let x1 := psel nm (psub O (rep O 843314856) x) x
  let sm := pmask (plt O (rep O 210828714) x1)
  let z := psel sm (Nat.sub (rep O 421657428) x1) x1
  (z, sm, nm)

noncomputable def out28 (O sm nm s c : Nat) : Nat × Nat :=
  let sv := psel sm c s
  let cv := psel sm s c
  (Nat.add (Nat.mul O 4611686018427387904) sv,
    psel nm (Nat.sub (Nat.mul O 4611686018427387904) cv) (Nat.add (Nat.mul O 4611686018427387904) cv))

noncomputable def rsh (O P sh : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.add P (Nat.mul O (Nat.shiftLeft 1 (Nat.sub sh 1)))) sh)
    (Nat.mul O (Nat.sub (Nat.shiftLeft 1 (Nat.sub 64 sh)) 1))

noncomputable def kc (O A c : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul A c) 28) (Nat.mul O 68719476735)

noncomputable def sqStep (O q : Nat) (s : Nat × Nat) : Nat × Nat :=
  let t := Nat.add s.2 (Nat.mul O q)
  let ge := Nat.sub O (plt O s.1 t)
  (Nat.sub s.1 (Nat.land t (pmask ge)), Nat.add (pshr1 O s.2) (Nat.mul ge q))

noncomputable def sqLoop (O K : Nat) (s : Nat × Nat) : Nat × Nat :=
  @Nat.rec (fun _ => Nat × Nat → Nat × Nat) (fun s => s)
    (fun k ih s => ih (sqStep O (Nat.shiftLeft 1 (Nat.add k k)) s)) K s

noncomputable def psqrt (O W : Nat) : Nat :=
  Nat.add (sqLoop O 29 (psub O W (Nat.mul O 4611686018427387904), 0)).2 (Nat.mul O 4611686018427387904)

end D3Ck2
