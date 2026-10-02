import Lean
import Tammes15.Solution

/-! For the badges of ci.yml: the hypotheses of the main theorem (its binders whose type is a
proposition) and the axioms they use. Run with `lake env lean code/lean/facts.lean`. -/

open Lean Meta in
#eval show MetaM Unit from do
  let mut hyps := 0
  let mut axs : Array Name := #[]
  for n in [``Tammes15.conjecture_of_enum_progTreesDom] do
    let c ← getConstInfo n
    hyps := hyps + (← forallTelescope c.type fun xs _ =>
      xs.foldlM (fun k x => do return if ← isProp (← inferType x) then k + 1 else k) 0)
    for a in ← collectAxioms n do
      unless axs.contains a do axs := axs.push a
  IO.println s!"hypotheses {hyps}"
  IO.println s!"axioms {axs.size}"
  IO.println s!"sorryAx {axs.contains ``sorryAx}"
