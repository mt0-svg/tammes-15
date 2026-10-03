import Tammes15.Challenge.Hyps.Computations
import Tammes15.Challenge.Attained.Data
import Tammes15.Challenge.Nonunique.Defs
import Tammes15.Challenge.PaperSteps.SearchDefs
import Tammes15.Challenge.PaperSteps.FrameDefs
import Tammes15.Challenge.Contractors.Defs

/-!
# Challenge

The statements of the fifteen theorems of `config.json`, for Comparator: `Tammes15.reduction`,
`Tammes15.fejesToth_bound`, `Tammes15.conjecture_of_enum_killed`, `Tammes15.nonunique_of_enum_killed`, and the eight
of `Tammes15.PaperSteps`: `Tammes15.PaperSteps.killed_of_progKilled`, `Tammes15.conjecture_of_enum_progKilled`,
`Tammes15.PaperSteps.progKilled_of_progTrees`, `Tammes15.conjecture_of_enum_progTrees`,
`Tammes15.PaperSteps.local_optimality_frame`, `Tammes15.PaperSteps.optima_four`,
`Tammes15.PaperSteps.frames_not_isometric` and `Tammes15.PaperSteps.frames_not_distance_preserving`, and the three
from the hypotheses of Theorem B.9 of the paper: `Tammes15.conjecture_of_enum_progTreesDom` (the theorem),
`Tammes15.Contractors.killed_of_progTreesDom` (D3) and `Tammes15.nonunique_of_enum_progTreesDom` (Corollary 1.2).
The modules `Tammes15.Challenge.*` are copies of the 24 modules that hold the definitions the statements reach
(the import closure of `Tammes15.Hyps.Computations`, `Tammes15.Attained.Data`, which defines the frames `frameC1` and
`frameC3`, `Tammes15.Nonunique.Defs`, which defines `contactGraph`, `Tammes15.PaperSteps.SearchDefs`, which defines
`ProgKilled`, `Procs`, `Procs.Sound` and `ProgTrees`, `Tammes15.PaperSteps.FrameDefs`, and
`Tammes15.Contractors.Defs`, which defines `Impl` and `ProgTreesDom` over the arithmetic of
`Tammes15.Contractors.Arith` and the primitive steps of `Tammes15.Contractors.Prims`), with their imports renamed and
nothing else changed (code/lean/challenge.sh writes them). Nothing in the package imports this file. Its fifteen
warnings, that the declarations use `sorry`, are expected: the proofs are in `Tammes15.Hyps.Reduction`,
`Tammes15.FejesToth.Bound`, `Tammes15.Attained.Final`, `Tammes15.Nonunique.Corollary`, the modules `Main`, `Search`,
`MainSearch`, `LocalEq`, `Optima` and `Isometric` of `Tammes15.PaperSteps`, and `Tammes15.Contractors.Statement` and
`Tammes15.Contractors.Main`, which Comparator checks against these statements.
-/

theorem Tammes15.reduction (L : Set Tammes15.PlaneGraph) (F : Set Tammes15.Frame)
    (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.Killed L F) (h4 : Tammes15.AttainedHyp F) : Tammes15.Conjecture := sorry

theorem Tammes15.fejesToth_bound : Tammes15.FejesTothBound := sorry

theorem Tammes15.conjecture_of_enum_killed (L : Set Tammes15.PlaneGraph) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.Killed L {Tammes15.Attained.frameC1, Tammes15.Attained.frameC3}) :
    Tammes15.Conjecture := sorry

theorem Tammes15.nonunique_of_enum_killed (L : Set Tammes15.PlaneGraph) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.Killed L {Tammes15.Attained.frameC1, Tammes15.Attained.frameC3}) :
    ∃ d : ℝ, IsGreatest {d | Tammes15.Achievable 15 d} d ∧
      ∃ X Y : Fin 15 → Tammes15.E3, (∀ i, ‖X i‖ = 1) ∧ (∀ i, ‖Y i‖ = 1) ∧
        (∀ i j, i ≠ j → d ≤ InnerProductGeometry.angle (X i) (X j)) ∧
        (∀ i j, i ≠ j → d ≤ InnerProductGeometry.angle (Y i) (Y j)) ∧
        IsEmpty (Tammes15.Nonunique.contactGraph X (Real.cos d) ≃g
          Tammes15.Nonunique.contactGraph Y (Real.cos d)) := sorry

theorem Tammes15.PaperSteps.killed_of_progKilled {L : Set Tammes15.PlaneGraph}
    (h : Tammes15.PaperSteps.ProgKilled L) :
    Tammes15.Killed L {Tammes15.Attained.frameC1, Tammes15.Attained.frameC3} := sorry

theorem Tammes15.conjecture_of_enum_progKilled (L : Set Tammes15.PlaneGraph)
    (h2 : Tammes15.EnumComplete L) (h3 : Tammes15.PaperSteps.ProgKilled L) :
    Tammes15.Conjecture := sorry

theorem Tammes15.PaperSteps.progKilled_of_progTrees {L : Set Tammes15.PlaneGraph}
    {N : Tammes15.PaperSteps.Procs} (h : Tammes15.PaperSteps.ProgTrees L N) (hN : N.Sound) :
    Tammes15.PaperSteps.ProgKilled L := sorry

theorem Tammes15.conjecture_of_enum_progTrees (L : Set Tammes15.PlaneGraph)
    (N : Tammes15.PaperSteps.Procs) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.PaperSteps.ProgTrees L N) (hN : N.Sound) :
    Tammes15.Conjecture := sorry

theorem Tammes15.PaperSteps.local_optimality_frame (keep : Fin 15 → Fin 18)
    (hkeep : Tammes15.PaperSteps.IsFrameKeep keep) (x : Fin 15 → Tammes15.E3) (hx : ∀ i, ‖x i‖ = 1)
    (R : Tammes15.E3 ≃ₗᵢ[ℝ] Tammes15.E3)
    (hxR : ∀ i, ‖x i - R (Tammes15.Attained.pt Tammes15.Attained.bR Tammes15.Attained.uR (keep i))‖ ≤
      Tammes15.rLocal) :
    Tammes15.PaperSteps.minAngle x ≤ Real.arccos Tammes15.Attained.uR ∧
      (Tammes15.PaperSteps.minAngle x = Real.arccos Tammes15.Attained.uR →
        ∃ R' : Tammes15.E3 ≃ₗᵢ[ℝ] Tammes15.E3,
          ∀ i, x i = R' (Tammes15.Attained.pt Tammes15.Attained.bR Tammes15.Attained.uR (keep i))) := sorry

theorem Tammes15.PaperSteps.optima_four :
    (∀ w : Fin 6, ∀ t : Fin 3 → Bool, ∃ t',
      Tammes15.PaperSteps.dWord w '' Tammes15.PaperSteps.frameSet t = Tammes15.PaperSteps.frameSet t') ∧
      Set.range Tammes15.Attained.frameC3.p = Tammes15.PaperSteps.frameSet (fun _ => true) ∧
      Set.range Tammes15.Attained.frameC1.p = Tammes15.PaperSteps.frameSet Tammes15.PaperSteps.tC1 ∧
      (∀ t, (∃ w, Tammes15.PaperSteps.dWord w '' Set.range Tammes15.Attained.frameC3.p =
        Tammes15.PaperSteps.frameSet t) ↔ ∀ i j, t i = t j) ∧
      (∀ t, (∃ w, Tammes15.PaperSteps.dWord w '' Set.range Tammes15.Attained.frameC1.p =
        Tammes15.PaperSteps.frameSet t) ↔ ¬ ∀ i j, t i = t j) := sorry

theorem Tammes15.PaperSteps.frames_not_isometric :
    ¬ ∃ O : Tammes15.E3 ≃ᵢ Tammes15.E3,
      O '' Set.range Tammes15.Attained.frameC1.p = Set.range Tammes15.Attained.frameC3.p := sorry

theorem Tammes15.PaperSteps.frames_not_distance_preserving :
    ¬ ∃ σ : Fin 15 ≃ Fin 15, ∀ i j,
      ‖Tammes15.Attained.frameC3.p (σ i) - Tammes15.Attained.frameC3.p (σ j)‖ =
        ‖Tammes15.Attained.frameC1.p i - Tammes15.Attained.frameC1.p j‖ := sorry

theorem Tammes15.Contractors.killed_of_progTreesDom {L : Set Tammes15.PlaneGraph} {N : Tammes15.PaperSteps.Procs}
    (h3 : Tammes15.Contractors.ProgTreesDom L N)
    (hN : Tammes15.Contractors.Impl N) : Tammes15.Killed L {Tammes15.Attained.frameC1, Tammes15.Attained.frameC3} := sorry

theorem Tammes15.conjecture_of_enum_progTreesDom (L : Set Tammes15.PlaneGraph) (N : Tammes15.PaperSteps.Procs)
    (h2 : Tammes15.EnumComplete L) (h3 : Tammes15.Contractors.ProgTreesDom L N) (hN : Tammes15.Contractors.Impl N) :
    Tammes15.Conjecture := sorry

theorem Tammes15.nonunique_of_enum_progTreesDom (L : Set Tammes15.PlaneGraph) (N : Tammes15.PaperSteps.Procs)
    (h2 : Tammes15.EnumComplete L) (h3 : Tammes15.Contractors.ProgTreesDom L N) (hN : Tammes15.Contractors.Impl N) :
    ∃ d : ℝ, IsGreatest {d | Tammes15.Achievable 15 d} d ∧
      ∃ X Y : Fin 15 → Tammes15.E3, (∀ i, ‖X i‖ = 1) ∧ (∀ i, ‖Y i‖ = 1) ∧
        (∀ i j, i ≠ j → d ≤ InnerProductGeometry.angle (X i) (X j)) ∧
        (∀ i j, i ≠ j → d ≤ InnerProductGeometry.angle (Y i) (Y j)) ∧
        IsEmpty
          (Tammes15.Nonunique.contactGraph X (Real.cos d) ≃g Tammes15.Nonunique.contactGraph Y (Real.cos d)) := sorry
