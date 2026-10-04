import Tammes15.D3Kernel.Pent
import Tammes15.Trigrows.Rows

open Real

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel

noncomputable def hexOut (d x y z : ℝ) : ℝ := bangle d x + gam (ebase d z) (ebase d x) (ebase d y) + bangle d y

def InDomH (F0 F1 F2 F3 : ℕ) : Prop :=
  F0 < 2 ^ 64 ∧ F1 < 2 ^ 64 ∧ F2 < 2 ^ 64 ∧ F3 < 2 ^ 64 ∧
    0.9 ≤ fld F0 0 ∧ fld F0 32 ≤ 1 ∧ 1.1 ≤ fld F1 0 ∧ fld F1 32 ≤ 3.2 ∧ 1.1 ≤ fld F2 0 ∧ fld F2 32 ≤ 3.2 ∧
    1.1 ≤ fld F3 32 ∧ fld F3 32 ≤ 3.2

def LaneClaimH (hi : Bool) (F0 F1 F2 F3 : ℕ) : Prop :=
  ∀ d x y z : ℝ, fld F0 0 ≤ d → d ≤ fld F0 32 → fld F1 0 ≤ x → x ≤ fld F1 32 → fld F2 0 ≤ y → y ≤ fld F2 32 →
    x < π → y < π → z < π → (if hi then 0 < z ∧ z ≤ fld F3 32 else fld F3 32 ≤ z) →
      Claim hi (fld F3 0) (hexOut d x y z)

theorem hex_fc {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k} (hA : RelSys P H A)
    {e : P.G.Dart} (he : fsize P e = 6) : A.fc e 0 = hexOut A.d (A.fc e 1) (A.fc e 5) (A.fc e 3) := by
  rw [(hA.hex e he).2.2.2.1, hexOut]
  ring

end Tammes15.D3Trig
