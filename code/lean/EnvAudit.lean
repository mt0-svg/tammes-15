import Lean

/-!
# Environment audit of a module or namespace prefix

`check.sh` (step 6) writes a file that imports the audited modules, then this file without its `import`
line, then one `#env_audit` command. Each argument of the command is a scope: `"M:P"` takes every
constant declared in a module whose name starts with `P`, `"N:P"` every constant whose name (private
prefix removed) starts with `P`, whatever its module.

For the constants in scope it prints the number per module; the flagged ones (declared `axiom`,
`unsafe`, `partial def`, other `opaque`, `implemented_by`, `extern`); then `AXIOMS OK` when every
axiom reached through the whole dependency graph (imports included) is `propext`,
`Classical.choice` or `Quot.sound`, otherwise the axioms reached and, for each, the constants in
scope that reach it (`sorryAx` for a `sorry`, `Lean.ofReduceBool` for `native_decide`, a declared
axiom).

The graph is walked here from the constant values; the precomputed axiom lists that `#print axioms`
reads from imported modules are not used.
-/

open Lean Elab Command

namespace LeanAudit

/-- The constants that `ci` refers to, as `Lean.CollectAxioms` walks them. -/
def usedConstants (ci : ConstantInfo) : Array Name :=
  let used (e : Expr) := e.getUsedConstants
  match ci with
  | .axiomInfo v => used v.type
  | .defnInfo v => used v.type ++ used v.value
  | .thmInfo v => used v.type ++ used v.value
  | .opaqueInfo v => used v.type ++ used v.value
  | .quotInfo v => used v.type
  | .ctorInfo v => used v.type
  | .recInfo v => used v.type
  | .inductInfo v => used v.type ++ v.ctors.toArray

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#env_audit" scopes:str* : command => do
  let env ← getEnv
  let scopes := scopes.map (·.getString)
  let modPre := scopes.filterMap fun s => if s.startsWith "M:" then some (toString (s.drop 2)).toName else none
  let nsPre := scopes.filterMap fun s => if s.startsWith "N:" then some (toString (s.drop 2)).toName else none
  -- The constants in scope, with their module.
  let mut found : Array (Name × Name) := #[]
  for (c, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    let user := (privateToUserName? c).getD c
    if modPre.any (·.isPrefixOf m) || nsPre.any (·.isPrefixOf user) then
      found := found.push (c, m)
  let mine := found.qsort (fun a b => a.1.toString < b.1.toString)
  let mut perModule : Std.HashMap Name Nat := {}
  for (_, m) in mine do
    perModule := perModule.insert m (perModule.getD m 0 + 1)
  let rows := perModule.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (m, k) in rows do
    logInfo m!"MODULE {m}: {k} constants"
  logInfo m!"SCOPE {scopes}: {mine.size} constants in {rows.size} modules"
  -- Flags. `f._unsafe_rec` is the compiled code of a recursive definition `f`: a shim when `f` is a
  -- checked definition, the mark of `partial def f` when `f` is opaque.
  let mut shims : Nat := 0
  let mut flags : Nat := 0
  for (c, m) in mine do
    let some ci := env.find? c | continue
    let base := c.getPrefix
    if let .str _ "_unsafe_rec" := c then
      match env.find? base with
      | some (.opaqueInfo _) => logWarning m!"FLAG partial def: {base} ({m})"; flags := flags + 1
      | _ => shims := shims + 1
      continue
    let say (what : String) := logWarning m!"FLAG {what}: {c} ({m})"
    match ci with
    | .axiomInfo _ => say "axiom"; flags := flags + 1
    | .opaqueInfo _ =>
      unless env.contains (c ++ `_unsafe_rec) do say "opaque"; flags := flags + 1
    | .defnInfo v =>
      if v.safety == .partial then say "partial"; flags := flags + 1
    | _ => pure ()
    if ci.isUnsafe then say "unsafe"; flags := flags + 1
    if let some t := Compiler.getImplementedBy? env c then
      say s!"implemented_by {t}"; flags := flags + 1
    if isExtern env c then say "extern"; flags := flags + 1
  logInfo m!"FLAGS: {flags} ({shims} compiled-code shims `_unsafe_rec` of checked recursive definitions not counted)"
  -- The dependency graph from the constants in scope.
  let mut visited : NameSet := {}
  let mut axs : NameSet := {}
  let mut stack : List Name := mine.toList.map (·.1)
  repeat
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      let some ci := env.find? c | continue
      if let .axiomInfo _ := ci then axs := axs.insert c
      for d in usedConstants ci do
        unless visited.contains d do stack := d :: stack
  let reached := axs.toList.map toString |>.toArray.qsort (· < ·)
  let bad := axs.toList.filter (!stdAxioms.contains ·)
  if bad.isEmpty then
    let only := if reached.isEmpty then "no axiom" else s!"only the axioms {reached.toList}"
    logInfo m!"AXIOMS OK: {mine.size} constants reach {visited.size} constants and {only}"
    return
  logError m!"AXIOMS NOT OK: reached {reached}"
  let inScope : NameSet := mine.foldl (fun s p => s.insert p.1) {}
  -- Reverse edges of the graph, to find what reaches each axiom.
  let mut rev : Std.HashMap Name (Array Name) := {}
  for c in visited.toList do
    let some ci := env.find? c | continue
    for d in usedConstants ci do
      rev := rev.alter d fun | none => some #[c] | some a => some (a.push c)
  for a in bad do
    -- Everything that reaches `a`, by the reverse edges.
    let mut seen : NameSet := {}
    let mut todo : List Name := [a]
    repeat
      match todo with
      | [] => break
      | c :: rest =>
        todo := rest
        for u in rev.getD c #[] do
          unless seen.contains u do
            seen := seen.insert u
            todo := u :: todo
    let direct := (rev.getD a #[]).filter inScope.contains
    let hit := mine.filter (seen.contains ·.1)
    logError m!"AXIOM {a}: reached by {hit.size} constants in scope, {direct.size} of them directly"
    for c in direct.qsort (·.toString < ·.toString) do
      logError m!"DIRECT {a}: {c}"
    for (c, _) in (hit.filter (!direct.contains ·.1)).extract 0 30 do
      logError m!"REACHES {a}: {c}"
    if hit.size - direct.size > 30 then
      logError m!"REACHES {a}: {hit.size - direct.size - 30} more not listed"

end LeanAudit
