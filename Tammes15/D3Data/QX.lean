import Tammes15.D3Data.Q
import Tammes15.D3Data.HintKill
import Tammes15.D3Data.AlphaX
import Tammes15.D3Trig.HexSub

namespace Tammes15.D3Data

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.D3Kernel.Kinds Tammes15.D3Kernel.Pent
  Tammes15.D3Kernel.Walk

theorem progOKH_skip0 {hi : Bool} {p : Prog} (h : D3Trig.ProgOKH hi p) : D3Trig.ProgOKH hi (skip0 p) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  have hv' : Nat.beq (p (oN n) F0 F1 F2 F3 hs) v = true := by
    unfold skip0 at hv
    rw [oN_ne_zero (by omega)] at hv
    exact hv
  exact h n F0 F1 F2 F3 hs v hD hv' l hl h1

noncomputable def hexProgsZ (i : ℕ) : Prog := skip0 (D3Trig.hexProgs i)

noncomputable def QXs : List (ℕ × Checker) :=
  [(0, linChecker), (2, D3Trig.rhoChecker rhoProgsZ), (1, alphaCheckerX), (7, boundChecker),
    (4, D3Trig.hexCheckerS hexProgsZ), (10, hintKill localOK), (11, hintKill pairOK)]

theorem QXs_sound : ∀ p ∈ QXs, p.2.Sound (kindIs p.1) := by
  intro p hp
  simp only [QXs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact linChecker_sound
  · exact D3Trig.rhoChecker_sound rhoProgsZ fun i hi => progOKR_skip0 (D3Trig.rhoProgs_ok i hi)
  · exact alphaCheckerX_sound
  · exact boundChecker_sound
  · exact D3Trig.hexCheckerS_sound hexProgsZ fun i hi => progOKH_skip0 (D3Trig.hexProgs_ok i hi)
  · exact hintLocal_sound
  · exact hintPair_sound

noncomputable def QX : Checker := byKind ((3, pentChecker progsZ) :: QXs)

def mkHX (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 r0 r1 r2 r3 h0 h1 h2 h3 h4 h5 lc pr : List ℕ) : QX.H :=
  (((((p0, p1), (p2, p3)), ((p4, p5), (p6, p7))), (((p8, p9), (p10, p11)), (((), ()), ((), ())))),
    ((), ((((r0, r1), (r2, r3))), ((), ((), ((((h0, h1), (h2, h3)), ((h4, h5), ((), ()))), (lc, (pr, ()))))))))

theorem killedCode_of_QX {R s t : List ℕ} (h : Reach QX R s t) (ht : Done t) {c : GCode}
    (hc : cover c R = true) : KilledCode c :=
  killedCode_of_kinds progsZ progsZ_ok QXs QXs_sound cover_sound h ht hc

end Tammes15.D3Data
