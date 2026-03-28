/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Init.LawfulBEqTactics

namespace Lean.Elab.Deriving.ReflBEq
open Lean.Parser.Term
open Meta

open TSyntax.Compat in
open Parser.Tactic in
def mkReflBEqInstanceCmds (declName : Name) : TermElabM (Array Syntax) := do
  let indVal ← getConstInfoInduct declName
  if indVal.all.length > 1 then
    throwError "Deriving `ReflBEq` for mutual inductives is not supported"
  if indVal.isNested then
    throwError "Deriving `ReflBEq` for nested inductives is not supported"

  let argNames     ← mkInductArgNames indVal
  let binders      ← mkImplicitBinders argNames
  let binders      := binders ++ (← mkInstImplicitBinders ``BEq indVal argNames)
  let binders      := binders ++ (← mkInstImplicitBinders ``ReflBEq indVal argNames)
  let indType      ← mkInductiveApp indVal argNames
  let type         ← `($(mkCIdent ``ReflBEq) $indType)
  let instCmd ← `( instance $binders:implicitBinder* : $type where
    rfl := by deriving_ReflEq_tactic)
  let cmds := #[instCmd]
  trace[Elab.Deriving.reflBEq] "\n{cmds}"
  return cmds

open Command

def mkReflBEqInstance (declName : Name) : CommandElabM Unit := do
  withoutExposeFromCtors declName do
    let cmds ← liftTermElabM <| mkReflBEqInstanceCmds declName
    cmds.forM elabCommand

def mkReflBEqInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      mkReflBEqInstance declName
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler ``ReflBEq mkReflBEqInstanceHandler
  registerTraceClass `Elab.Deriving.reflBEq

end Lean.Elab.Deriving.ReflBEq
