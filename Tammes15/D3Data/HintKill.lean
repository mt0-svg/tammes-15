import Tammes15.D3Kernel.Kinds.Local
import Tammes15.D3Kernel.Kinds.Pair

namespace Tammes15.D3Data

open Tammes15 Tammes15.D3Kernel Tammes15.D3Kernel.Kinds

def hkAll (ok : ℕ → ℕ → ℕ → Bool) (l : List (ℕ × ℕ)) : List ℕ → Bool :=
  @List.rec (ℕ × ℕ) (fun _ => List ℕ → Bool)
    (fun hs => @List.rec ℕ (fun _ => Bool) true (fun _ _ _ => false) hs)
    (fun p _ ih hs => @List.rec ℕ (fun _ => Bool) false
      (fun h hs' _ => ok p.1 p.2 (Nat.shiftLeft h (nat_lit 128)) && ih hs') hs)
    l

def hintKill (ok : ℕ → ℕ → ℕ → Bool) : Checker where
  σ := Bool × List (ℕ × ℕ)
  H := List ℕ
  init := (true, [])
  onRec _ _ _ s := (false, s.2)
  onKill g box _ s := (s.1, (g, box) :: s.2)
  fin s hs := s.1 && hkAll ok s.2 hs
  frc s k := @Bool.rec (fun _ => List ℕ) (k (false, s.2)) (k (true, s.2)) s.1
  frc_eq s k := by cases s with | mk b l => cases b <;> rfl

theorem hkAll_mem {ok : ℕ → ℕ → ℕ → Bool} : ∀ {l : List (ℕ × ℕ)} {hs : List ℕ}, hkAll ok l hs = true →
    ∀ p ∈ l, ∃ h, ok p.1 p.2 (Nat.shiftLeft h 128) = true
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], hh, _, _ => absurd (hh : false = true) Bool.false_ne_true
  | q :: l, h :: hs, hh, p, hp => by
    have hq : (ok q.1 q.2 (Nat.shiftLeft h 128) && hkAll ok l hs) = true := hh
    rw [Bool.and_eq_true] at hq
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨h, hq.1⟩
    · exact hkAll_mem hq.2 p hp

theorem hint_fold (ok : ℕ → ℕ → ℕ → Bool) :
    ∀ (l : List Ev) (s : Bool × List (ℕ × ℕ)),
      (l.foldl (fun s e => (hintKill ok).step e s) s).1 = true →
        s.1 = true ∧ (∀ p ∈ s.2, p ∈ (l.foldl (fun s e => (hintKill ok).step e s) s).2) ∧
          ∀ e ∈ l, ∃ g box it, e = Ev.kill g box it ∧
            (g, box) ∈ (l.foldl (fun s e => (hintKill ok).step e s) s).2 := by
  intro l
  induction l with
  | nil => exact fun s h => ⟨h, fun _ hp => hp, fun e he => by simp at he⟩
  | cons ev l ih =>
    intro s h
    change (List.foldl (fun s e => (hintKill ok).step e s) ((hintKill ok).step ev s) l).1 = true at h
    obtain ⟨h1, hmem, hall⟩ := ih _ h
    change ((hintKill ok).step ev s).1 = true at h1
    change ∀ p ∈ ((hintKill ok).step ev s).2, _ at hmem
    change s.1 = true ∧ (∀ p ∈ s.2, p ∈ (List.foldl (fun s e => (hintKill ok).step e s)
      ((hintKill ok).step ev s) l).2) ∧ ∀ e ∈ ev :: l, ∃ g box it, e = Ev.kill g box it ∧
        (g, box) ∈ (List.foldl (fun s e => (hintKill ok).step e s) ((hintKill ok).step ev s) l).2
    cases ev with
    | record g box it => exact absurd (h1 : false = true) Bool.false_ne_true
    | kill g box it =>
      refine ⟨h1, fun p hp => hmem p (List.mem_cons_of_mem _ hp), fun e he => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨g, box, it, rfl, hmem (g, box) List.mem_cons_self⟩
      · exact hall e he

theorem hintKill_sound (ok : ℕ → ℕ → ℕ → Bool) (hok : ∀ g box it, ok g box it = true → KillOK g box)
    (adm : ℕ → Prop) : (hintKill ok).Sound adm := by
  intro tr h _ hfin
  change ((Checker.run (hintKill ok) tr).1 && hkAll ok (Checker.run (hintKill ok) tr).2 h) = true at hfin
  rw [Bool.and_eq_true] at hfin
  obtain ⟨_, _, hall⟩ := hint_fold ok tr (hintKill ok).init hfin.1
  intro e he
  obtain ⟨g, box, it, rfl, hmem⟩ := hall e he
  obtain ⟨k, hk⟩ := hkAll_mem hfin.2 _ hmem
  exact hok g box _ hk

theorem hintLocal_sound : (hintKill localOK).Sound (kindIs 10) :=
  hintKill_sound localOK (fun _ _ _ h => localOK_sound h) _

theorem hintPair_sound : (hintKill pairOK).Sound (kindIs 11) :=
  hintKill_sound pairOK (fun _ _ _ h => pairOK_sound h) _

theorem hintPairV_sound : (hintKill pairVOK).Sound (kindIs 11) :=
  hintKill_sound pairVOK (fun _ _ _ h => pairVOK_sound h) _

end Tammes15.D3Data
