import Tammes15.D3Kernel.Kinds.Keys

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.D3Kernel Pent

def boundKill (g box it : ℕ) : Bool :=
  let v := fk it 64 127
  let lo := bk box (Nat.shiftLeft v 1)
  let hi := bk box (Nat.add (Nat.shiftLeft v 1) 1)
  Nat.blt v (nvK g) && kgood lo && kgood hi && Nat.blt (kfix hi) (kfix lo)

def boundChecker : Checker where
  σ := Bool
  H := Unit
  init := true
  onRec _ _ _ _ := false
  onKill g box it s := s && boundKill g box it
  fin s _ := s
  frc s k := @Bool.rec (fun _ => List ℕ) (k false) (k true) s
  frc_eq s k := by cases s <;> rfl

theorem killOK_of_boundKill {g box it : ℕ} (h : boundKill g box it = true) : KillOK g box := by
  simp only [boundKill] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, nvK_eq] at h
  obtain ⟨⟨⟨hv, hlo⟩, hhi⟩, hlt⟩ := h
  intro s hS
  obtain ⟨b1, b2⟩ := hS _ hv
  have e1 : bk box (Nat.shiftLeft (fk it 64 127) 1) = bnd box (2 * fk it 64 127) := by
    rw [bk_eq, shl_eq, mul_comm, pow_one]
  have e2 : bk box (Nat.add (Nat.shiftLeft (fk it 64 127) 1) 1) = bnd box (2 * fk it 64 127 + 1) := by
    rw [bk_eq, shl_eq, mul_comm, pow_one]
  have k1 := keyVal_kgood hlo
  have k2 := keyVal_kgood hhi
  rw [e1] at k1
  rw [e2] at k2
  rw [e1, e2] at hlt
  rw [k1] at b1
  rw [k2] at b2
  have hlt' : (kfix (bnd box (2 * fk it 64 127 + 1)) : ℝ) < kfix (bnd box (2 * fk it 64 127)) := by
    exact_mod_cast hlt
  have := lt_of_le_of_lt (b1.trans b2) (div_lt_div_of_pos_right hlt' (by positivity))
  exact absurd this (lt_irrefl _)

theorem bound_fold : ∀ (l : List Ev) (s : Bool),
    l.foldl (fun s e => boundChecker.step e s) s = true → s = true ∧ ∀ e ∈ l, e.OK := by
  intro l
  induction l with
  | nil => exact fun s h => ⟨h, fun e he => by simp at he⟩
  | cons ev l ih =>
    intro s h
    change List.foldl (fun s e => boundChecker.step e s) (boundChecker.step ev s) l = true at h
    obtain ⟨h1, hl⟩ := ih _ h
    cases ev with
    | record g box it => exact absurd h1 (by change ¬ false = true; simp)
    | kill g box it =>
      change (s && boundKill g box it) = true at h1
      rw [Bool.and_eq_true] at h1
      refine ⟨h1.1, fun e he => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact killOK_of_boundKill h1.2
      · exact hl e he

theorem boundChecker_sound : boundChecker.Sound (kindIs 7) := by
  intro tr _ _ hfin
  exact (bound_fold tr boundChecker.init hfin).2

end Tammes15.D3Kernel.Kinds
