/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Lean.Elab.Command
import Lean.Linter.Util

set_option linter.missingDocs true

namespace Lean.Linter

open Lean Elab Command
open Lean.Linter (logLint)

/--
A linter that warns when bound variable names are the same as constructor names for their types,
modulo namespaces.
 -/
register_builtin_option linter.constructorNameAsVariable : Bool := {
  defValue := true,
  descr := "enable the linter that warns when bound variable names are nullary constructor names"
}

/--
Reports when bound variables' names overlap with constructor names for their type. This is to warn
especially new users that they have built a pattern that matches anything, rather than one that
matches a particular constructor. Use `linter.constructorNameAsVariable` to disable.
-/
def constructorNameAsVariable : Linter where
  run cmdStx := do
    let some cmdStxRange := cmdStx.getRange?
      | return

    let infoTrees := (← get).infoState.trees.toArray
    let warnings : IO.Ref (Std.HashMap String.Range (Syntax × Name × Name)) ← IO.mkRef {}

    for tree in infoTrees do
      tree.visitM' (postNode := fun ci info _ => do
        match info with
        | .ofTermInfo ti =>
          match ti.expr with
          | .fvar id .. =>
            let some range := info.range? | return
            if (← warnings.get).contains range then return
            let .original .. := info.stx.getHeadInfo | return
            if ti.isBinder then
              -- This is a local variable declaration.
              let some ldecl := ti.lctx.find? id | return
              -- Skip declarations which are outside the command syntax range, like `variable`s
              -- (it would be confusing to lint these), or those which are macro-generated
              if !cmdStxRange.contains range.start || ldecl.userName.hasMacroScopes then return
              let opts := ci.options
              -- we have to check for the option again here because it can be set locally
              if !linter.constructorNameAsVariable.get opts then return
              if let n@(.str .anonymous s) := info.stx.getId then
                -- Check whether the type is an inductive type, and get its constructors
                let ty ←
                  if let some t := ti.expectedType? then pure t
                  else ti.runMetaM ci (Meta.inferType ti.expr)
                let ty ← ti.runMetaM ci (instantiateMVars ty >>= Meta.whnf)
                if let .const tn _ := ty.getAppFn' then
                  if let some (.inductInfo i) := (← getEnv).find? tn then
                    for c in i.ctors do
                      -- Only warn when the constructor has 0 fields. Pattern variables can't be
                      -- confused with constructors that want arguments.
                      if let some (.ctorInfo ctorInfo) := (← getEnv).find? c then
                        if ctorInfo.numFields > 0 then continue
                      if let .str _ cn := c then
                        if cn == s then
                          warnings.modify (·.insert range (info.stx, n, c))
            else pure ()
          | _ => pure ()
        | _ => pure ())

    -- Sort the outputs by position
    for (_range, declStx, userName, ctorName) in (← warnings.get).toArray.qsort (·.1.start < ·.1.start) do
      logLint linter.constructorNameAsVariable declStx <|
        m!"Local variable '{userName}' resembles constructor '{ctorName}' - " ++
        m!"write '.{userName}' (with a dot) or '{ctorName}' to use the constructor."

builtin_initialize addLinter constructorNameAsVariable
