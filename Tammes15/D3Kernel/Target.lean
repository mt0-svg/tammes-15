import Tammes15.W1Filter.Statement
import Tammes15.D3lp.Kill

namespace Tammes15.D3Kernel

open Tammes15 Tammes15.D3lp Tammes15.W1Filter

abbrev frames : Set Frame := {Attained.frameC1, Attained.frameC3}

def codesOfLits : List ℕ → List GCode
  | D :: f :: s :: t => ⟨D, f, s⟩ :: codesOfLits t
  | _ => []

def CodeSet (ls : List (List ℕ)) : Set GCode :=
  {c | ∃ l ∈ ls, c ∈ codesOfLits l}

def KilledCode (c : GCode) : Prop :=
  ∀ (P : PlaneGraph) (lab : P.G.Dart ≃ Fin c.D), Matches P c lab → KilledEntry frames P

def JobFact (job : List (List ℕ)) : Prop :=
  ∀ l ∈ job, ∀ c ∈ codesOfLits l, KilledCode c

theorem killed_of_codes {ls : List (List ℕ)} (h : ∀ l ∈ ls, ∀ c ∈ codesOfLits l, KilledCode c) :
    Killed (LOf (CodeSet ls)) frames := by
  intro P hP
  obtain ⟨c, ⟨l, hl, hc⟩, lab, hm⟩ := hP
  exact h l hl c hc P lab hm

theorem killed_of_jobs (jobs : List (List (List ℕ))) (h : ∀ J ∈ jobs, JobFact J) :
    Killed (LOf (CodeSet jobs.flatten)) frames :=
  killed_of_codes fun l hl c hc => by
    obtain ⟨J, hJ, hlJ⟩ := List.mem_flatten.mp hl
    exact h J hJ l hlJ c hc

theorem conjecture_of_jobs (S : Set (List ℕ)) (jobs : List (List (List ℕ))) (h1 : EnumCompletePC S)
    (h2 : RunW1 S (CodeSet jobs.flatten)) (h : ∀ J ∈ jobs, JobFact J) : Conjecture :=
  conjecture_of_plantri_run S _ h1 h2 (killed_of_jobs jobs h)

theorem main_two (job₀ job₁ : List (List ℕ)) :
    JobFact job₀ → JobFact job₁ → Killed (LOf (CodeSet (job₀ ++ job₁))) frames := fun h₀ h₁ => by
  have := killed_of_jobs [job₀, job₁] (by
    intro J hJ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
    rcases hJ with rfl | rfl
    · exact h₀
    · exact h₁)
  simpa using this

end Tammes15.D3Kernel
