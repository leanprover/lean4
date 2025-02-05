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

/--
`set_option linter.index_variables true` enables a strict linter that
validates that the only variables appearing as an index (e.g. in `xs[i]` or `xs.take i`)
are `i`, `j`, or `k`.
-/
register_builtin_option linter.index_variables : Bool := {
  defValue := false
  descr := "Validate that variables appearing as an index (e.g. in `xs[i]` or `xs.take i`) are only `i`, `j`, or `k`."
}

open Lean Elab Command

-- def numericalIndex? (stx : Syntax) : Option Syntax :=
--   if stx.isOfKind ``«term__[_]» || stx.isOfKind ``«term__[_]'_» then
--     some stx[2]
--   else if stx.isOfKind ``«term__[_]_?» then
--     some stx[3]
--   else
--     none

-- /-- Return the syntax for the arguments of all "numerical indices" appearing in the given syntax. -/
-- partial def numericalIndices (stx : Syntax) : Array Syntax :=
--   match numericalIndex? stx with
--   | some idx => #[idx]
--   | none => stx.getArgs.flatMap numericalIndices

partial def numericalIndices' (t : InfoTree) : MetaM (Array (Syntax × Name)) := do
  -- logInfo (← t.format)
  let r ← t.foldInfoM (init := #[]) fun _ info r => do
    let stx := info.stx
    if let .ofTermInfo info := info then
      let idx? := match_expr info.expr with
      | GetElem?.getElem? _ _ _ _ _ _ i => some i
      | List.take _ i _ => some i
      | _ => none
      match idx? with
      | some (.fvar i) =>
        match info.lctx.find? i with
        | some ldecl => return r.push (stx, ldecl.userName)
        | none => return r
      | _ => return r
    else
      return r
  return r

/--
A linter which validates that the only variables used as "indices" (e.g. in `xs[i]` or `xs.take i`)
are `i`, `j`, or `k`.
-/
def indexLinter : Linter
  where run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.index_variables (← getOptions) do return
    if (← get).messages.hasErrors then return
    if ! (← getInfoState).enabled then return
    let trees ← getInfoTrees
    for t in trees do
      for (idxStx, n) in ← liftCoreM ((numericalIndices' t).run' {} {}) do
        if n != `i && n != `j && n != `k then
          Linter.logLint linter.index_variables idxStx
            m!"Forbidden variable appearing as an index: use `i`, `j`, or `k`: {n}\n{toString idxStx}"

    -- for idxStx in numericalIndices stx do
    --   if idxStx.isIdent then
    --     let ident := idxStx.getId
    --     if ident != `i && ident != `j && ident != `k then
    --       Linter.logLint linter.index_variables idxStx
    --         m!"Forbidden variable appearing as an index: use `i`, `j`, or `k`: {ident}"

builtin_initialize addLinter indexLinter
#eval `(term| xs.drop i)
