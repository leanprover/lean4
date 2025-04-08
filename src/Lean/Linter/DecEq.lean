/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Lean.Elab.Command
import Lean.Server.InfoUtils
set_option linter.missingDocs true -- keep it documented

/-!
This file defines a linter for the conversion between the `LawfulBEq` and `DecidableEq` instance.
-/

namespace Lean.Linter.DecEq

/--
`set_option linter.decEqOfLawful true` enables a linter that validates that the instance
`instDecidableEqOfLawfulBEq` is not used within the type of a theorem.
-/
register_builtin_option linter.decEqOfLawful : Bool := {
  defValue := true
  descr := "Validate that DecidableEq is not accidentally synthesized from LawfulBEq"
}

/--
`set_option linter.beqOfDecEq true` enables a linter that validates that the
`instBEqOfDecidableEq` instance is not used when the type is a variable.
-/
register_builtin_option linter.beqOfDecEq : Bool := {
  defValue := false
  descr := "Validate that BEq is not accidentally synthesized from DecidableEq (when the type is a variable)"
}

open Lean Elab Command

/--
A linter which validates that `instDecidableEqOfLawfulBEq` is not used in the declaration type.
-/
def decEqOfLawfulLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless (← getOptions).get linter.decEqOfLawful.name true do return
    if (← get).messages.hasErrors then return
    if ! (← getInfoState).enabled then return
    for t in ← getInfoTrees do
      if let .context _ _ := t then -- Only consider info trees with top-level context
        t.foldInfoM (fun ci i _  => do
          match i with
          | .ofTermInfo term =>
            unless term.isBinder do return
            unless term.expr.isConst do return
            let type := (← ci.runCoreM <| getConstVal term.expr.constName!).type
            if let some e := type.find? (fun e => e.isConstOf ``instDecidableEqOfLawfulBEq) then
              Lean.Linter.logLint linter.decEqOfLawful term.stx
                m!"Binder uses 'instDecidableEqOfLawfulBEq', consider adding a [DecidableEq ...] instance assumption to avoid this"
          | _ => pure ()
        ) ()

builtin_initialize addLinter decEqOfLawfulLinter

/--
A linter which validates that `instBEqOfDecidableEq` is not used in the declaration type when the type is a variable.
-/
def beqOfDecEqLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless (← getOptions).get linter.beqOfDecEq.name false do return
    if (← get).messages.hasErrors then return
    if ! (← getInfoState).enabled then return
    for t in ← getInfoTrees do
      if let .context _ _ := t then -- Only consider info trees with top-level context
        t.foldInfoM (fun ci i _  => do
          match i with
          | .ofTermInfo term =>
            unless term.isBinder do return
            unless term.expr.isConst do return
            let type := (← ci.runCoreM <| getConstVal term.expr.constName!).type
            if let some e := type.find? (fun e =>
                e.isAppOfArity ``instBEqOfDecidableEq 1 && e.appArg!.consumeMData.isBVar) then
              Lean.Linter.logLint linter.beqOfDecEq term.stx
                m!"Binder uses 'instBEqOfDecidableEq', consider adding [BEq ...] and [LawfulBEq ...] instance assumptions to avoid this"
          | _ => pure ()
        ) ()

builtin_initialize addLinter beqOfDecEqLinter

end Lean.Linter.DecEq
