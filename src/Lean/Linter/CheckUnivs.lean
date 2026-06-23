/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski

Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
module

prelude
public import Lean.Linter.Basic
public import Lean.Linter.Util
public import Lean.Util.CollectLevelParams
public import Lean.Util.ForEachExpr

public section

namespace Lean.Linter
open Elab Command Meta

/--
Enables the `checkUnivs` linter, which warns when a declaration has a universe parameter
that only ever occurs in a `max u v` together with another parameter, never on its own.
This usually means that the type contains a `max u v` where neither `u` nor `v` occur by
themselves; the fix is to provide the universe level explicitly.
-/
register_builtin_option linter.checkUnivs : Bool := {
  defValue := true
  descr := "enable the `checkUnivs` linter, which warns when a declaration has a universe \
    parameter that only ever occurs in a `max u v` together with another parameter, never \
    on its own."
}

namespace CheckUnivs

/--
`univParamsGrouped e nm₀` computes for each `Level` occurring in `e` the set of level parameters
that appear in it, returning the collection of such parameter sets.
In pseudo-mathematical form, this returns `{{p : parameter | p ∈ u} | (u : level) ∈ e}`.
Ignores `nm₀.proof_*` sub-constants.
-/
private def univParamsGrouped (e : Expr) (nm₀ : Name) : Std.HashSet (Array Name) :=
  runST fun _ =>
    let go : StateRefT (Std.HashSet (Array Name)) (ST _) Unit := e.forEach fun
      | .sort u =>
        modify (·.insert (CollectLevelParams.visitLevel u {}).params)
      | .const n us => do
        if let .str n s := n then
          if n == nm₀ && s.startsWith "proof_" then return
        modify (us.foldl (·.insert <| CollectLevelParams.visitLevel · {} |>.params))
      | _ => pure ()
    Prod.snd <$> go.run {}

/--
The good parameters are the parameters that occur somewhere in the set as a singleton or
(recursively) with only other good parameters.
All other parameters in the set are bad.
-/
private partial def badParams (l : Array (Array Name)) : Array Name :=
  let goodLevels := l.filterMap fun
    | #[u] => some u
    | _ => none
  if goodLevels.isEmpty then
    l.flatten.foldl (init := #[]) fun acc x => if acc.contains x then acc else acc.push x
  else
    badParams <| l.map (·.filter (!goodLevels.contains ·))

@[inherit_doc linter.checkUnivs]
def checkUnivsLinter : Linter where run := withSetOptionIn fun _ => do
  unless getLinterValue linter.checkUnivs (← getLinterOptions) do return
  if (← get).messages.hasErrors then return
  let env ← getEnv
  let mut seen : NameSet := {}
  for t in ← getInfoTrees do
    for declName in getNewDecls t do
      if seen.contains declName then continue
      seen := seen.insert declName
      let some info := env.find? declName | continue
      let bad := badParams (univParamsGrouped info.type declName).toArray
      unless bad.isEmpty do
        let univs := MessageData.joinSep (bad.toList.map fun u => m!"`{u}`") ", "
        logLintIf linter.checkUnivs (← getRef)
          m!"`{.ofConstName declName}`: universes {univs} only occur together. \
            This usually means there is a `max` expression in the type where none of these \
            universes appear on their own."

builtin_initialize addLinter checkUnivsLinter

end CheckUnivs
end Lean.Linter
