import Tammes15.PaperSteps.Relabel
import Tammes15.PaperSteps.Reflect
import Tammes15.PaperSteps.Targets
import Tammes15.Attained.Final

/-!
# D3 from the verdicts of the program

`killed_of_progKilled`: the verdicts of the program in its own conventions (`ProgKilled`) give D3,
`Killed L {frameC1, frameC3}`, by steps (i) to (iii) of the proof of Lemma B.7.
`conjecture_of_enum_progKilled` is the main theorem from D2 and these verdicts.
-/

namespace Tammes15.PaperSteps

open Tammes15

/-- D3 from the verdicts of the program. -/
theorem killed_of_progKilled {L : Set PlaneGraph} (h : ProgKilled L) :
    Killed L {Attained.frameC1, Attained.frameC3} := by
  intro P hP k hk H A hd1 hd2 hR
  obtain ⟨H₀, hsame, hkill⟩ := h P hP k hk H
  obtain ⟨σ, s, hs⟩ := exists_shift_data hsame
  have hR₀ : RelSys P H₀ (relabelAssign A σ s) := relSys_relabel σ s hs hR
  obtain ⟨g, hg, hfire⟩ := hkill (relabelAssign A σ s) hd1 hd2 hR₀
  refine ⟨relabelGlue g σ s, relabelGlue_valid hg σ s, ?_⟩
  have hY : ∀ a, glueY H A (relabelGlue g σ s) a =
      thetaL (progGlueY H₀ (relabelAssign A σ s) g (Equiv.sumCongr (Equiv.refl _) σ a)) := by
    intro a
    rw [glueY_relabel A σ s hs g a, glueY_theta hR₀ hg]
    rfl
  rcases hfire with hpair | htie
  · exact Or.inl (pairFires_of_equiv rfl _ (pAdj_sumMap σ) thetaL hY hpair)
  · exact Or.inr (localFires_of_equiv _ thetaL hY (localFires_of_tieFires htie))

end Tammes15.PaperSteps

namespace Tammes15

/-- `Tammes15.Conjecture` from `EnumComplete L` (D2) and the verdicts of the program on `L`. -/
theorem conjecture_of_enum_progKilled (L : Set PlaneGraph) (h2 : EnumComplete L)
    (h3 : PaperSteps.ProgKilled L) : Conjecture :=
  conjecture_of_enum_killed L h2 (PaperSteps.killed_of_progKilled h3)

end Tammes15
