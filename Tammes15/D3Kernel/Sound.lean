import Tammes15.D3Kernel.Sem

namespace Tammes15.D3Kernel

open Tammes15.D3lp Walk

theorem Checker.Sound.mono {Q : Checker} {adm adm' : ℕ → Prop} (h : Q.Sound adm)
    (himp : ∀ it, adm' it → adm it) : Q.Sound adm' :=
  fun tr hh hadm hfin => h tr hh (fun e he => himp _ (hadm e he)) hfin

theorem Checker.pair_step (sel : ℕ → Bool) (Q₁ Q₂ : Checker) (e : Ev) (s : Q₁.σ × Q₂.σ) :
    (Checker.pair sel Q₁ Q₂).step e s = bif sel e.it then (Q₁.step e s.1, s.2) else (s.1, Q₂.step e s.2) := by
  cases e <;> rfl

theorem Checker.pair_fold (sel : ℕ → Bool) (Q₁ Q₂ : Checker) (tr : List Ev) :
    ∀ (a : Q₁.σ) (b : Q₂.σ),
      tr.foldl (fun s e => (Checker.pair sel Q₁ Q₂).step e s) ((a, b) : (Checker.pair sel Q₁ Q₂).σ) =
        ((tr.filter fun e => sel e.it).foldl (fun s e => Q₁.step e s) a,
          (tr.filter fun e => !sel e.it).foldl (fun s e => Q₂.step e s) b) := by
  induction tr with
  | nil => intro a b; rfl
  | cons e tr ih =>
    intro a b
    have hstep := Checker.pair_step sel Q₁ Q₂ e (a, b)
    show List.foldl _ ((Checker.pair sel Q₁ Q₂).step e (a, b)) tr = _
    cases hs : sel e.it
    · simp only [hs, Bool.cond_false] at hstep
      rw [hstep, ih]
      simp only [List.filter_cons, hs, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, List.foldl_cons]
      rfl
    · simp only [hs, Bool.cond_true] at hstep
      rw [hstep, ih]
      simp only [List.filter_cons, hs, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, List.foldl_cons]
      rfl

theorem Checker.pair_sound {sel : ℕ → Bool} {Q₁ Q₂ : Checker} {adm : ℕ → Prop}
    (h₁ : Q₁.Sound fun it => adm it ∧ sel it = true) (h₂ : Q₂.Sound fun it => adm it ∧ sel it = false) :
    (Checker.pair sel Q₁ Q₂).Sound adm := by
  intro tr hh hadm hfin e he
  have hr := Checker.pair_fold sel Q₁ Q₂ tr Q₁.init Q₂.init
  have hf : (Q₁.fin ((Checker.pair sel Q₁ Q₂).run tr).1 hh.1 && Q₂.fin ((Checker.pair sel Q₁ Q₂).run tr).2 hh.2) =
    true := hfin
  have hrun : (Checker.pair sel Q₁ Q₂).run tr = (Q₁.run (tr.filter fun e => sel e.it),
      Q₂.run (tr.filter fun e => !sel e.it)) := hr
  rw [hrun, Bool.and_eq_true] at hf
  cases hs : sel e.it
  · refine h₂ _ hh.2 (fun e' he' => ?_) hf.2 e ?_
    · rw [List.mem_filter] at he'
      exact ⟨hadm e' he'.1, by simpa using he'.2⟩
    · rw [List.mem_filter]; exact ⟨he, by simp [hs]⟩
  · refine h₁ _ hh.1 (fun e' he' => ?_) hf.1 e ?_
    · rw [List.mem_filter] at he'
      exact ⟨hadm e' he'.1, he'.2⟩
    · rw [List.mem_filter]; exact ⟨he, hs⟩

theorem Checker.none_fold (tr : List Ev) : tr.foldl (fun s e => Checker.none.step e s) false = false := by
  induction tr with
  | nil => rfl
  | cons e tr ih => cases e <;> exact ih

theorem Checker.none_sound (adm : ℕ → Prop) : Checker.none.Sound adm := by
  intro tr hh _ hfin e he
  cases tr with
  | nil => simp at he
  | cons e' tr =>
    have h0 : Checker.none.run (e' :: tr) = false := by
      cases e' <;> exact Checker.none_fold tr
    have h1 : Checker.none.run (e' :: tr) = true := hfin
    rw [h0] at h1
    cases h1

def kindOf (it : ℕ) : ℕ := Nat.land (Nat.shiftRight it (nat_lit 71)) (nat_lit 15)

def byKind : List (ℕ × Checker) → Checker
  | [] => Checker.none
  | (κ, Q) :: l => Checker.pair (fun it => Nat.beq (kindOf it) κ) Q (byKind l)

theorem byKind_sound (l : List (ℕ × Checker)) (h : ∀ p ∈ l, p.2.Sound (kindIs p.1)) :
    (byKind l).Sound fun _ => True := by
  induction l with
  | nil => exact Checker.none_sound _
  | cons p l ih =>
    obtain ⟨κ, Q⟩ := p
    refine Checker.pair_sound ((h (κ, Q) (by simp)).mono fun it hit => ?_)
      ((ih fun p hp => h p (List.mem_cons_of_mem _ hp)).mono fun _ _ => trivial)
    have hk : kindOf it = κ := Nat.eq_of_beq_eq_true hit.2
    have hk' : kindOf it = itKind it := land_shiftRight it 71 4
    show itKind it = κ
    rw [← hk', hk]

def InvL : List ℕ → Prop
  | g :: box :: st => Inv g box st
  | _ => True

theorem reach_good {Q : Checker} (hQ : Q.Sound fun _ => True) {R s t : List ℕ} (h : Reach Q R s t)
    (ht : InvL t) : InvL s ∧ ∀ p ∈ rootPairs R, TreeKilled p.1 p.2 := by
  induction h with
  | refl s => exact ⟨ht, fun _ hp => by simp [rootPairs] at hp⟩
  | step d r hh hc _ ih =>
    obtain ⟨ht', hR⟩ := ih ht
    obtain ⟨g, box, st, c', tr, rfl, hs, hf, hrs, rfl⟩ := chk_spec hc
    have hok := hQ tr hh (fun _ _ => trivial) hf
    have hg' : Good c' := ⟨ht', by simp [hrs, rootPairs], by simp [hrs]⟩
    obtain ⟨hinv, hroots, hpar⟩ := steps_back hs hok hg'
    refine ⟨hinv, fun p hp => ?_⟩
    rw [rootPairs_append _ _ hpar, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hroots p hp
    · exact hR p hp

theorem reach_sound {Q : Checker} (hQ : Q.Sound fun _ => True) {R s t : List ℕ} (h : Reach Q R s t)
    (ht : Done t) : ∀ p ∈ rootPairs R, TreeKilled p.1 p.2 := by
  obtain ⟨g₀, rfl⟩ := ht
  have hu : InvL [g₀, 0] := ⟨fun ha => absurd ha not_active_zero, fun _ hm => by simp at hm⟩
  exact (reach_good hQ h hu).2

def CoverSound (cover : GCode → List ℕ → Bool) : Prop :=
  ∀ (c : GCode) (R : List ℕ), cover c R = true → (∀ p ∈ rootPairs R, TreeKilled p.1 p.2) → KilledCode c

theorem killedCode_of_walk {Q : Checker} (hQ : Q.Sound fun _ => True) {cover : GCode → List ℕ → Bool}
    (hcov : CoverSound cover) {R s t : List ℕ} (h : Reach Q R s t) (ht : Done t) {c : GCode}
    (hc : cover c R = true) : KilledCode c :=
  hcov c R hc (reach_sound hQ h ht)

end Tammes15.D3Kernel
