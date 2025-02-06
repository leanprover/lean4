/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.Command
import Lean.Server.InfoUtils
set_option linter.missingDocs true -- keep it documented

/-!
This file defines style linters for the `List`/`Array`/`Vector` modules.

Currently, we do not anticipate that they will be useful elsewhere.
-/

namespace Lean.Linter.List

/--
`set_option linter.indexVariables true` enables a strict linter that
validates that the only variables appearing as an index (e.g. in `xs[i]` or `xs.take i`)
are `i`, `j`, or `k`.
-/
register_builtin_option linter.indexVariables : Bool := {
  defValue := false
  descr := "Validate that variables appearing as an index (e.g. in `xs[i]` or `xs.take i`) are only `i`, `j`, or `k`."
}

open Lean Elab Command

/--
Return the syntax for all expressions in which an `fvarId` appears as a "numerical index", along with the user name of that `fvarId`.
-/
partial def numericalIndices (t : InfoTree) : List (Syntax × Name) :=
  t.deepestNodes fun _ info _ => do
    let stx := info.stx
    if let .ofTermInfo info := info then
      let idx? := match_expr info.expr with
      | GetElem.getElem _ _ _ _ _ _ i _ => some i
      | GetElem?.getElem? _ _ _ _ _ _ i => some i
      | List.take _ i _ => some i
      | List.drop _ i _ => some i
      | List.set _ _ i _ => some i
      | List.insertIdx _ i _ _ => some i
      | List.eraseIdx _ _ i _ => some i
      | _ => none
      match idx? with
      | some (.fvar i) =>
        match info.lctx.find? i with
        | some ldecl => some (stx, ldecl.userName)
        | none => none
      | _ => none
    else
      none

/--
A linter which validates that the only variables used as "indices" (e.g. in `xs[i]` or `xs.take i`)
are `i`, `j`, or `k`.
-/
def indexLinter : Linter
  where run := withSetOptionIn fun stx => do
    -- We intentionally do not use `getLinterValue` here, as we do *not* want to opt in to `linter.all`.
    unless (← getOptions).get linter.indexVariables.name false do return
    if (← get).messages.hasErrors then return
    if ! (← getInfoState).enabled then return
    for t in ← getInfoTrees do
      if let .context _ _ := t then -- Only consider info trees with top-level context
      for (idxStx, n) in numericalIndices t do
        if n != `i && n != `j && n != `k then
          Linter.logLint linter.indexVariables idxStx
            m!"Forbidden variable appearing as an index: use `i`, `j`, or `k`: {n}"

builtin_initialize addLinter indexLinter

end Lean.Linter.List
