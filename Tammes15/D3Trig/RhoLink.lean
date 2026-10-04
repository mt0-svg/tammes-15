import Tammes15.D3Kernel.Pent
import Tammes15.Trigrows.Mono

open Real

namespace Tammes15.D3Trig

open Tammes15 Tammes15.D3Kernel

def LaneClaimR (k : Fin 2) (hi : Bool) (F0 F1 F2 F3 : ℕ) : Prop :=
  ∀ d x y : ℝ, fld F0 0 ≤ d → d ≤ fld F0 32 → fld F1 0 ≤ x → x ≤ fld F1 32 → fld F2 0 ≤ y → y ≤ fld F2 32 →
    x < π → y = rho d x → Claim hi (fld F3 0) (if k = 0 then y else d)

theorem rhombus_fc {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {A : Assign P k} (hA : RelSys P H A)
    {e : P.G.Dart} (he : fsize P e = 4) : A.fc e 1 = rho A.d (A.fc e 0) ∧ A.fc e 3 = rho A.d (A.fc e 0) := by
  refine ⟨(hA.rhombus e he).2, ?_⟩
  have h2 : fsize P ((P.R.face ^ 2) e) = 4 := by rw [D3lp.fsize_face_pow]; exact he
  have hr := (hA.rhombus _ h2).2
  rw [D3lp.fc_face_pow, D3lp.fc_face_pow] at hr
  rw [hr, (hA.rhombus e he).1]

end Tammes15.D3Trig
