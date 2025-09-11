/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Lean.Data.Options
public import Lean.Meta.Tactic.Simp.Types
import Init.Simproc
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Meta.Eqns
import Lean.Meta.SameCtorUtils
import Lean.Meta.MethodSpecs
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Simp.Rewrite

namespace Lean.Elab.Deriving.ReflBEq
open Lean.Parser.Term
open Meta

-- TODO: Should this be moved to MethodSpecs?
public section
builtin_simproc_decl simpBEq (_ == _) := fun e => do
  let_expr BEq.beq _ inst lhs rhs ← e | return .continue
  unless inst.getAppFn.isConst do return .continue
  let some _ ← isConstructorApp? lhs | return .continue
  let some _ ← isConstructorApp? rhs | return .continue
  let some thm ← getMethodSpecTheorem inst.getAppFn.constName! "beq" | return .continue
  let simpThms ← mkSimpTheoremFromConst thm
  assert! simpThms.size = 1
  let some r ← Simp.tryTheorem? e simpThms[0]! | return .continue
  return .visit r
end

open TSyntax.Compat in
open Parser.Tactic in
def mkReflBEqInstanceCmds (declName : Name) : TermElabM (Array Syntax) := do
  let indVal ← getConstInfoInduct declName

  -- let specThms ← forallTelescopeReducing indVal.type fun xs _ => do
  --   let t := mkAppN (← mkConstWithLevelParams declName) xs
  --   let beqInstType ← mkAppM ``BEq #[t]
  --   let beqInst ← synthInstance beqInstType
  --   unless beqInst.getAppFn.isConst do
  --     throwError "cannot derive ReflBEq for instance {beqInst}"
  --   let beqInstConst := beqInst.getAppFn.constName!
  --   let some thms ← getMethodSpecTheorems beqInstConst "beq"
  --     | throwError "instance {.ofConstName beqInstConst} has no method spec theorems. Try `@[method_specs]`"
  --   pure thms

  -- let mut simpArgs : TSyntaxArray ``simpArg := #[← `(simpArg | *)]
  -- for thm in specThms do
  --   simpArgs := simpArgs.push (← `(simpArg | $(mkCIdent thm)))

  let argNames     ← mkInductArgNames indVal
  let binders      ← mkImplicitBinders argNames
  let binders      := binders ++ (← mkInstImplicitBinders ``BEq indVal argNames)
  let binders      := binders ++ (← mkInstImplicitBinders ``ReflBEq indVal argNames)
  let indType      ← mkInductiveApp indVal argNames
  let type         ← `($(mkCIdent ``ReflBEq) $indType)
  let instCmd ← `(instance $binders:implicitBinder* : $type := by
    constructor
    intro x
    induction x
    all_goals
      first | simp [ *, $(mkCIdent ``simpBEq):ident ]
            | fail "Failed to prove ReflBEq instance")
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
