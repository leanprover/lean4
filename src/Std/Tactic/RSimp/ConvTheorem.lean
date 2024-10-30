/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Std.Tactic.RSimp.Setup
import Std.Tactic.RSimp.Fuel
import Lean.Elab.Tactic
import Lean.Elab.DeclUtil
import Lean.Elab.Command
import Lean.Elab.Tactic.Conv
import Init.Tactics
import Init.Conv

open Lean.Parser.Tactic in
/--
TODO
-/
syntax (name := convTheorem) declModifiers "conv_theorem" declId declSig " => " Conv.convSeq : command

open Lean.Parser.Tactic in
syntax (name := withFuel) "withFuel" " => " Conv.convSeq : conv

syntax (name := abstractAs) "abstractAs " nestedDeclModifiers ident : conv

open Lean Meta Elab Command Tactic Conv

@[tactic withFuel] def evalWithFuel : Tactic := fun stx => do
  let lhs ← getLhs
  withMainContext do
    -- TODO: This needs to generalize some variables first
    let (rhs, proof) ← convert lhs (evalTactic stx[2])
    if lhs == rhs then
      throwError "Non-productive recursive equation {lhs} = {rhs}."
    else if let some (rhs', proof') ← recursionToFuel? lhs rhs proof then
      updateLhs rhs' proof'
    else
      throwError "Did not find {lhs} in {rhs}."

@[tactic abstractAs] def evalAbstractAs : Tactic := fun stx => do
  let lhs ← getLhs
  let modifiers ← elabModifiers ⟨stx[1]⟩
  let declId := stx[2]
  let ⟨_, declName, _⟩ ← Term.expandDeclId (← getCurrNamespace) (← Term.getLevelNames) declId modifiers
  let e ← mkAuxDefinition (compile := false) declName (← inferType lhs) lhs
  withSaveInfoContext <| Term.addTermInfo' declId e.getAppFn (isBinder := true)
  changeLhs e

def convert (lhs : Expr) (conv : TacticM Unit) : TermElabM (Expr × Expr) := do
  let (rhs, newGoal) ← Conv.mkConvGoalFor lhs
  let _ ← Tactic.run newGoal.mvarId! do
    conv
    for mvarId in (← getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    pruneSolvedGoals
    unless (← getGoals).isEmpty do
      throwError "convert tactic failed, there are unsolved goals\n{goalsToMessageData (← getGoals)}"
  return (← instantiateMVars rhs, ← instantiateMVars newGoal)

@[command_elab convTheorem]
def elabConvTheorem : CommandElab := fun stx => do
  let modifiers ← elabModifiers ⟨stx[0]⟩
  let declId            := stx[2]
  let (binders, lhsStx) := expandDeclSig stx[3]
  runTermElabM fun vars => do
    let scopeLevelNames ← Term.getLevelNames
    let ⟨shortName, declName, allUserLevelNames⟩ ← Term.expandDeclId (← getCurrNamespace) scopeLevelNames declId modifiers
    addDeclarationRangesForBuiltin declName modifiers.stx stx
    Term.withAutoBoundImplicitForbiddenPred (fun n => shortName == n) do
    Term.withDeclName declName <| Term.withLevelNames allUserLevelNames <| Term.elabBinders binders.getArgs fun xs => do
      Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.beforeElaboration
      let lhs ← Term.elabTermAndSynthesize lhsStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let lhs ← instantiateMVars lhs
      let (rhs, value) ← convert lhs (Tactic.evalTactic stx[5])
      let eqType ← mkEq lhs rhs
      let type ← mkForallFVars xs eqType
      let type ← mkForallFVars vars type
      let type ← Term.levelMVarToParam type
      let value ← mkLambdaFVars xs value
      let value ← mkLambdaFVars vars value
      let usedParams  := collectLevelParams {} type |>.params
      match sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams with
      | Except.error msg      => throwErrorAt stx msg
      | Except.ok levelParams =>
        let type ← instantiateMVars type
        let value ← instantiateMVars value

        let decl := Declaration.thmDecl {
          name        := declName,
          levelParams := levelParams,
          type        := type,
          value       := value,
        }
        Term.ensureNoUnassignedMVars decl
        addDecl decl
        withSaveInfoContext do
          Term.addTermInfo' declId (← mkConstWithLevelParams declName) (isBinder := true)
        Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.afterTypeChecking
        Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.afterCompilation



conv_theorem test : id 1 + 2 =>
  skip
  unfold id
  simp

/-- info: test : id 1 + 2 = 3 -/
#guard_msgs in
#check test

conv_theorem test2 (a b c : Fin 12) : (a + b + c).val =>
  simp [Fin.ext_iff, Fin.val_add]
  abstractAs /-- docstrings possible! -/ test2_rhs

/--
info: def test2_rhs : Fin 12 → Fin 12 → Fin 12 → Nat :=
fun a b c => (↑a + ↑b + ↑c) % 12
-/
#guard_msgs in
#print test2_rhs

/-- info: test2 (a b c : Fin 12) : ↑(a + b + c) = test2_rhs a b c -/
#guard_msgs in
#check test2

/-- error: unknown identifier 'foo' -/
#guard_msgs in
conv_theorem bad_elab1 : foo && true => skip

-- TODO: Why does this not abort nicely

/--
error: unknown identifier 'foo'
---
error: (kernel) declaration has metavariables 'bad_elab2'
-/
#guard_msgs in
conv_theorem bad_elab2 : foo true => skip

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

conv_theorem fib_optimize : fib =>
  withFuel =>
    ext n
    unfold fib
    simp [← Nat.add_eq]
  abstractAs fib.opt

/--
info: def fib.opt : Nat → Nat :=
rsimp_iterate fib fun ih n =>
  match n with
  | 0 => 0
  | 1 => 1
  | n.succ.succ => (ih n).add (ih (n.add 1))
-/
#guard_msgs in
#print fib.opt

def fib' (n : Nat) := (fib n, fib (n+1))
