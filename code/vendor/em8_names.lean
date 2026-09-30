import Tammes15.Vendor.EM8.BestPacking
import Lean

/-!
Where the declarations of the vendored eight-point library (modules `Tammes15.Vendor.EM8.*`) sit: the
number under each root namespace, whether a module outside the library (Mathlib and its dependencies)
declares a constant under the same root (an extension of a Mathlib namespace), and the number under
the package namespace `Tammes15.Vendor.EM8`. Internal and private names are counted apart.
Run: lake env lean code/vendor/em8_names.lean > code/vendor/em8_names.out
-/

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let pre := `Tammes15.Vendor.EM8
  let pkg := `Tammes15.Vendor.EM8
  let mut nmods : Std.HashSet Name := {}
  let mut inPkg := 0
  let mut internal := 0
  let mut internalOut : Array Name := #[]
  let mut roots : Std.HashMap Name Nat := {}
  let mut otherRoots : Std.HashSet Name := {}
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    if !pre.isPrefixOf m then
      otherRoots := otherRoots.insert n.getRoot
      continue
    nmods := nmods.insert m
    if n.isInternalDetail || isPrivateName n then
      internal := internal + 1
      let s := n.toString (escape := false)
      if !((s.splitOn pkg.toString).length > 1 || (s.splitOn (pkg.toString.replace "." "_")).length > 1) then
        internalOut := internalOut.push n
      continue
    if pkg.isPrefixOf n then inPkg := inPkg + 1
    roots := roots.insert n.getRoot (roots.getD n.getRoot 0 + 1)
  IO.println s!"modules of the library: {nmods.size}"
  IO.println s!"declarations: {roots.fold (fun a _ c => a + c) 0}; under {pkg}: {inPkg}; internal or private (not counted): {internal}"
  IO.println "roots of the declarations, their number, and whether Mathlib or its dependencies declare under the same root:"
  for (r, c) in roots.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"  {r}: {c}; declared outside the library too: {otherRoots.contains r}"
  IO.println s!"internal or private names whose text does not contain {pkg} (dots or underscores): {internalOut.size}"
  for n in (internalOut.qsort (fun a b => a.toString < b.toString)).extract 0 20 do
    IO.println s!"  {n}"
