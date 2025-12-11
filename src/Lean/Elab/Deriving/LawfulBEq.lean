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

namespace Lean.Elab.Deriving.LawfulBEq
open Lean.Parser.Term
open Meta

open TSyntax.Compat in
open Parser.Tactic in
def mkLawfulBEqInstanceCmds (declName : Name) : TermElabM (Array Syntax) := do
  let indVal ← getConstInfoInduct declName
  if indVal.all.length > 1 then
    throwError "Deriving `LawfulBEq` for mutual inductives is not supported"
  if indVal.isNested then
    throwError "Deriving `LawfulBEq` for nested inductives is not supported"

  let argNames     ← mkInductArgNames indVal
  let binders      ← mkImplicitBinders argNames
  let binders      := binders ++ (← mkInstImplicitBinders ``BEq indVal argNames)
  let binders      := binders ++ (← mkInstImplicitBinders ``LawfulBEq indVal argNames)
  let indType      ← mkInductiveApp indVal argNames
  let type         ← `($(mkCIdent ``LawfulBEq) $indType)
  let instCmd ← `(
    instance $binders:implicitBinder* : $type := LawfulBEq.mk (by deriving_LawfulEq_tactic)
  )
  let cmds := #[instCmd]
  trace[Elab.Deriving.lawfulBEq] "\n{cmds}"
  return cmds

open Command

def mkLawfulBEqInstance (declName : Name) : CommandElabM Unit := do
  withoutExposeFromCtors declName do
    let cmds ← liftTermElabM <| mkLawfulBEqInstanceCmds declName
    cmds.forM elabCommand

def mkLawfulBEqInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      mkLawfulBEqInstance declName
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler ``LawfulBEq mkLawfulBEqInstanceHandler
  registerTraceClass `Elab.Deriving.lawfulBEq

end Lean.Elab.Deriving.LawfulBEq
