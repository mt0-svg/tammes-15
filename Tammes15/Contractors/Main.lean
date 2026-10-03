import Tammes15.Contractors.Statement
import Tammes15.Nonunique.Corollary

/-!
# D3 and Corollary 1.2 from the trees of the program (Theorem B.9 of the paper)

`Contractors.killed_of_progTreesDom`: the replayed trees of the program with root boxes in
the domain (`ProgTreesDom`) and how its procedures compute (`Impl`) give D3,
`Killed L {frameC1, frameC3}`. `nonunique_of_enum_progTreesDom` is Corollary 1.2
(`nonunique_of_enum_killed`) from D2 and these hypotheses, as `conjecture_of_enum_progTreesDom`
is the main theorem from them.
-/

namespace Tammes15.Contractors

open Tammes15 Tammes15.PaperSteps

/-- D3 from the trees of the program on `L` with root boxes in the domain, and how its procedures
compute. -/
theorem killed_of_progTreesDom {L : Set PlaneGraph} {N : Procs} (h3 : ProgTreesDom L N)
    (hN : Impl N) : Killed L {Attained.frameC1, Attained.frameC3} :=
  killed_of_progKilled (progKilled_of_progTrees (progTrees_onDom hN h3) (Impl.onDom_sound hN))

end Tammes15.Contractors

namespace Tammes15

open Real InnerProductGeometry

/-- Corollary 1.2 from `EnumComplete L` (D2), the replayed trees of the program on `L` with
root boxes in the domain, and how its procedures compute (`Contractors.Impl`). -/
theorem nonunique_of_enum_progTreesDom (L : Set PlaneGraph) (N : PaperSteps.Procs)
    (h2 : EnumComplete L) (h3 : Contractors.ProgTreesDom L N) (hN : Contractors.Impl N) :
    ∃ d : ℝ, IsGreatest {d | Achievable 15 d} d ∧
      ∃ X Y : Fin 15 → Tammes15.E3, (∀ i, ‖X i‖ = 1) ∧ (∀ i, ‖Y i‖ = 1) ∧
        (∀ i j, i ≠ j → d ≤ angle (X i) (X j)) ∧ (∀ i j, i ≠ j → d ≤ angle (Y i) (Y j)) ∧
        IsEmpty (Nonunique.contactGraph X (cos d) ≃g Nonunique.contactGraph Y (cos d)) :=
  nonunique_of_enum_killed L h2 (Contractors.killed_of_progTreesDom h3 hN)

end Tammes15
