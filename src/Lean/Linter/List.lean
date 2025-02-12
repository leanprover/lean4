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

/--
`set_option linter.listVariables true` enables a strict linter that
validates that all `List`/`Array`/`Vector` variables use standardized names.
-/
register_builtin_option linter.listVariables : Bool := {
  defValue := false
  descr := "Validate that all `List`/`Array`/`Vector` variables use allowed names."
}

open Lean Elab Command

/--
Return the syntax for all expressions in which an `fvarId` appears as a "numerical index", along with the user name of that `fvarId`.
-/
def numericalIndices (t : InfoTree) : List (Syntax × Name) :=
  (t.deepestNodes fun _ info _ => do
    let stx := info.stx
    if let .ofTermInfo info := info then
      let idxs := match_expr info.expr with
      | GetElem.getElem _ _ _ _ _ _ i _ => [i]
      | GetElem?.getElem? _ _ _ _ _ _ i => [i]
      | List.take _ i _ => [i]
      | List.drop _ i _ => [i]
      | List.set _ _ i _ => [i]
      | List.insertIdx _ i _ _ => [i]
      | List.eraseIdx _ _ i _ => [i]
      | List.zipIdx _ _ i => [i]
      | _ => []
      match idxs with
      | [] => none
      | _ => idxs.filterMap fun i =>
        match i with
        | .fvar i =>
          match info.lctx.find? i with
          | some ldecl => some (stx, ldecl.userName)
          | none => none
        | _ => none
    else
      none).flatten

/-- Find all binders appearing in the given info tree. -/
def binders (t : InfoTree) (p : Expr → Bool := fun _ => true) : IO (List (Syntax × Name × Expr)) :=
  t.collectTermInfoM fun ctx ti => do
    if ti.isBinder then do
      -- Something is wrong here: sometimes `inferType` fails with an unknown fvar error,
      -- despite passing the local context here.
      -- We fail quietly by returning a `Unit` type.
      let ty ← ctx.runMetaM ti.lctx do instantiateMVars (← (Meta.inferType ti.expr) <|> pure (.const `Unit []))
      if p ty then
        if let .fvar i := ti.expr then
          match ti.lctx.find? i with
          | some ldecl => return some (ti.stx, ldecl.userName, ty)
          | none => return none
        else
          return none
      else
        return none
    else
      return none

/-- Allowed names for index variables. -/
def allowedIndices : List String := ["i", "j", "k"]

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
        if let .str _ n := n then
          if !allowedIndices.contains n then
            Linter.logLint linter.indexVariables idxStx
              m!"Forbidden variable appearing as an index: use `i`, `j`, or `k`: {n}"

builtin_initialize addLinter indexLinter

/-- Strip optional suffixes from a binder name. -/
def stripBinderName (s : String) : String :=
  s.stripSuffix "'" |>.stripSuffix "₁" |>.stripSuffix "₂" |>.stripSuffix "₃"

/-- Allowed names for `List` variables. -/
def allowedListNames : List String := ["l", "r", "s", "t", "tl", "ws", "xs", "ys", "zs", "as", "bs", "cs", "acc"]

/-- Allowed names for `Array` variables. -/
def allowedArrayNames : List String := ["ws", "xs", "ys", "zs", "as", "bs", "cs"]

/-- Allowed names for `Vector` variables. -/
def allowedVectorNames : List String := ["ws", "xs", "ys", "zs", "as", "bs", "cs"]

/--
A linter which validates that all `List`/`Array`/`Vector` variables use allowed names.
-/
def listVariablesLinter : Linter
  where run := withSetOptionIn fun stx => do
    unless (← getOptions).get linter.listVariables.name false do return
    if (← get).messages.hasErrors then return
    if ! (← getInfoState).enabled then return
    for t in ← getInfoTrees do
      if let .context _ _ := t then -- Only consider info trees with top-level context
        let binders ← binders t
        for (stx, n, ty) in binders.filter fun (_, _, ty) => ty.isAppOf `List do
          if let .str _ n := n then
          let n := stripBinderName n
          if !allowedListNames.contains n then
            unless (ty.getArg! 0).isAppOf `List && n == "L" do
              Linter.logLint linter.listVariables stx
                m!"Forbidden variable appearing as a `List` name: {n}"
        for (stx, n, _) in binders.filter fun (_, _, ty) => ty.isAppOf `Array do
          if let .str _ n := n then
          let n := stripBinderName n
          if !allowedArrayNames.contains n then
            Linter.logLint linter.listVariables stx
              m!"Forbidden variable appearing as a `Array` name: {n}"
        for (stx, n, _) in binders.filter fun (_, _, ty) => ty.isAppOf `Vector do
          if let .str _ n := n then
          let n := stripBinderName n
          if !allowedVectorNames.contains n then
            Linter.logLint linter.listVariables stx
              m!"Forbidden variable appearing as a `Vector` name: {n}"

builtin_initialize addLinter listVariablesLinter

end Lean.Linter.List
