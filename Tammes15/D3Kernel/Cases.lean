import Tammes15.D3Kernel.Target
import Tammes15.PaperSteps.Main

namespace Tammes15.D3Kernel

open Tammes15 Tammes15.D3lp

def CaseKilled (P : PlaneGraph) {k : ℕ} (H₀ : HexChoice P k) (lo hi : ℝ) : Prop :=
  ∀ A : Assign P k, lo ≤ A.d → A.d ≤ hi → dlo ≤ A.d → A.d ≤ dhi → RelSys P H₀ A →
    ∃ g : GlueData P k, g.Valid ∧
      (PairFires P A (PaperSteps.progGlueY H₀ A g) ∨ PaperSteps.TieFires (PaperSteps.progGlueY H₀ A g))

def CasesKilled (P : PlaneGraph) : Prop :=
  ∀ k : ℕ, P.n + k = 15 → ∀ H : HexChoice P k, ∃ H₀ : HexChoice P k, PaperSteps.SameHexSet H H₀ ∧
    ∀ d : ℝ, dlo ≤ d → d ≤ dhi → ∃ lo hi : ℝ, lo ≤ d ∧ d ≤ hi ∧ CaseKilled P H₀ lo hi

theorem killedEntry_of_casesKilled {P : PlaneGraph} (h : CasesKilled P) : KilledEntry frames P := by
  have hp : PaperSteps.ProgKilled {P} := by
    intro Q hQ k hk H
    rw [Set.mem_singleton_iff] at hQ
    subst hQ
    obtain ⟨H₀, hs, hK⟩ := h k hk H
    refine ⟨H₀, hs, fun A h1 h2 hR => ?_⟩
    obtain ⟨lo, hi, hlo, hhi, hc⟩ := hK A.d h1 h2
    exact hc A hlo hhi h1 h2 hR
  exact PaperSteps.killed_of_progKilled hp P rfl

theorem killedCode_of_casesKilled {c : GCode}
    (h : ∀ (P : PlaneGraph) (lab : P.G.Dart ≃ Fin c.D), Matches P c lab → CasesKilled P) :
    KilledCode c :=
  fun P lab hm => killedEntry_of_casesKilled (h P lab hm)

theorem killedCode_of_rootKilled {c : GCode}
    (h : ∀ (P : PlaneGraph) (lab : P.G.Dart ≃ Fin c.D), Matches P c lab → RootKilled P dlo dhi) :
    KilledCode c :=
  fun P lab hm => killedEntry_of_rootKilled (h P lab hm)

end Tammes15.D3Kernel
