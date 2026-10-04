import Tammes15.D3Kernel.Pent

namespace Tammes15.D3Kernel

open Tammes15.D3lp Walk Pent

theorem killedCode_of_kinds (progs : ℕ → Prog) (hp : ∀ i < 12, ProgOK (kOf i) (hiOf i) (progs i))
    (Qs : List (ℕ × Checker)) (hQs : ∀ p ∈ Qs, p.2.Sound (kindIs p.1)) {cover : GCode → List ℕ → Bool}
    (hcov : CoverSound cover) {R s t : List ℕ} (h : Reach (byKind ((3, pentChecker progs) :: Qs)) R s t)
    (ht : Done t) {c : GCode} (hc : cover c R = true) : KilledCode c := by
  refine killedCode_of_walk (byKind_sound _ ?_) hcov h ht hc
  intro p hp'
  rcases List.mem_cons.mp hp' with rfl | hq
  · exact pentChecker_sound progs hp
  · exact hQs p hq

end Tammes15.D3Kernel
