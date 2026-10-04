import Tammes15.D3Data.Alpha
import Tammes15.D3Kernel.Assembly
import Tammes15.D3Kernel.Kinds.Bound
import Tammes15.D3Kernel.Kinds.Cover
import Tammes15.D3Prog.Bridge
import Tammes15.D3Trig.Rho

namespace Tammes15.D3Data

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel Tammes15.D3Kernel.Kinds Tammes15.D3Kernel.Pent
  Tammes15.D3Kernel.Walk

def skip0 (p : Prog) : Prog :=
  fun O F0 F1 F2 F3 hs => @Bool.rec (fun _ => ℕ) (p O F0 F1 F2 F3 hs) 0 (Nat.beq O 0)

theorem oN_ne_zero {n : ℕ} (h : 0 < n) : Nat.beq (oN n) 0 = false := by
  refine Bool.eq_false_iff.mpr fun h0 => ?_
  revert h0
  refine fun h0 => absurd (Nat.eq_of_beq_eq_true h0) ?_
  unfold oN
  show (Nat.shiftLeft 1 (Nat.shiftLeft n 6) - 1) / 18446744073709551615 ≠ 0
  rw [shl_eq, shl_eq, one_mul]
  have h1 : 2 ^ 64 ≤ 2 ^ (n * 2 ^ 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 18446744073709551615 ≤ 2 ^ (n * 2 ^ 6) - 1 := by
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    omega
  exact (Nat.div_pos h2 (by norm_num)).ne'

theorem progOK_skip0 {k : Fin 2} {hi : Bool} {p : Prog} (h : ProgOK k hi p) : ProgOK k hi (skip0 p) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  have hv' : Nat.beq (p (oN n) F0 F1 F2 F3 hs) v = true := by
    unfold skip0 at hv
    rw [oN_ne_zero (by omega)] at hv
    exact hv
  exact h n F0 F1 F2 F3 hs v hD hv' l hl h1

theorem progOKR_skip0 {k : Fin 2} {hi : Bool} {p : Prog} (h : D3Trig.ProgOKR k hi p) :
    D3Trig.ProgOKR k hi (skip0 p) := by
  intro n F0 F1 F2 F3 hs v hD hv l hl h1
  have hv' : Nat.beq (p (oN n) F0 F1 F2 F3 hs) v = true := by
    unfold skip0 at hv
    rw [oN_ne_zero (by omega)] at hv
    exact hv
  exact h n F0 F1 F2 F3 hs v hD hv' l hl h1

noncomputable def progsZ (i : ℕ) : Prog := skip0 (D3Prog.progs i)

noncomputable def rhoProgsZ (i : ℕ) : Prog := skip0 (D3Trig.rhoProgs i)

theorem progsZ_ok : ∀ i < 12, ProgOK (kOf i) (hiOf i) (progsZ i) :=
  fun i hi => progOK_skip0 (D3Prog.progs_ok i hi)

noncomputable def Qs : List (ℕ × Checker) :=
  [(0, linChecker), (2, D3Trig.rhoChecker rhoProgsZ), (1, alphaChecker), (7, boundChecker)]

theorem Qs_sound : ∀ p ∈ Qs, p.2.Sound (kindIs p.1) := by
  intro p hp
  simp only [Qs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact linChecker_sound
  · exact D3Trig.rhoChecker_sound rhoProgsZ fun i hi => progOKR_skip0 (D3Trig.rhoProgs_ok i hi)
  · exact alphaChecker_sound
  · exact boundChecker_sound

noncomputable def Q : Checker := byKind ((3, pentChecker progsZ) :: Qs)

def mkH (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 r0 r1 r2 r3 : List ℕ) : Q.H :=
  (((((p0, p1), (p2, p3)), ((p4, p5), (p6, p7))), (((p8, p9), (p10, p11)), (((), ()), ((), ())))),
    ((), ((((r0, r1), (r2, r3))), ((), ((), ())))))

theorem Reach.trans {Q : Checker} {R₁ R₂ s t u : List ℕ} (h₁ : Reach Q R₁ s t) (h₂ : Reach Q R₂ t u) :
    Reach Q (R₁ ++ R₂) s u := by
  induction h₁ with
  | refl s => exact h₂
  | step d r h hc _ ih =>
    rw [List.append_assoc]
    exact Reach.step d r h hc (ih h₂)

theorem killedCode_of_Q {R s t : List ℕ} (h : Reach Q R s t) (ht : Done t) {c : GCode} (hc : cover c R = true) :
    KilledCode c :=
  killedCode_of_kinds progsZ progsZ_ok Qs Qs_sound cover_sound h ht hc

end Tammes15.D3Data
