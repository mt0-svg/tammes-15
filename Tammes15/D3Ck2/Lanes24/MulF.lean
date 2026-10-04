import Tammes15.D3Ck2.Lanes24.Base

namespace Lanes24

noncomputable def mulBitF (O A B k P : Nat) (ih : Nat → Nat) : Nat :=
  frc2 (Nat.add P (Nat.land (Nat.shiftLeft A k)
    (Nat.mul (Nat.land B (Nat.shiftLeft O k)) (Nat.sub (Nat.shiftLeft 1 (Nat.sub 64 k)) 1)))) 1 (fun P _ => ih P)

noncomputable def mulF (K : Nat) (O A B : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun P => P) (fun k ih P => mulBitF O A B k P ih) K 0

end Lanes24
