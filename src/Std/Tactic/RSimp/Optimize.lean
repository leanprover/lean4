/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Std.Tactic.RSimp.Setup
import Std.Tactic.RSimp.Fuel
import Lean.Elab.Tactic
import Init.Tactics

open Lean Meta

-- TODO: Namespace

initialize registerTraceClass `tactic.rsimp_optimize

def getEqUnfold (declName : Name) : MetaM (Option (Expr × Expr)) := do
  -- TODO: Make nicer, and move near the eqUnfold definition
  if (← getUnfoldEqnFor? declName (nonRec := false)).isSome then
    let unfold := .str declName eqUnfoldThmSuffix
    executeReservedNameAction unfold
    let unfoldProof ← mkConstWithLevelParams unfold
    let some (_, _, rhs) := (← inferType unfoldProof).eq? | throwError "Unexpected type of {unfold}"
    return some (rhs, unfoldProof)
  else return none

def optimize (declName : Name) : MetaM Unit := do
  let opt_name := .str declName "rsimp"
  let proof_name := .str declName "eq_rsimp"
  if (← getEnv).contains opt_name then throwError "{opt_name} has already been declared"
  if (← getEnv).contains proof_name then throwError "{proof_name} has already been declared"

  let info ← getConstInfoDefn declName
  let lhs := mkConst declName (info.levelParams.map mkLevelParam)
  let (rhs0, rwProof) ←
    if let some (rhs, unfoldProof) ← getEqUnfold declName then
      pure (rhs, unfoldProof)
    else
      let unfoldProof ← mkEqRefl lhs
      pure (info.value, unfoldProof)

  -- Do we need to give the user control over the simplifier here?
  -- TODO: Unify with rsimp_decide
  let .some se ← getSimpExtension? `rsimp | throwError "simp set 'rsimp' not found"
  let ctx : Simp.Context := { config := {}, simpTheorems := #[(← se.getTheorems)], congrTheorems := (← Meta.getSimpCongrTheorems) }
  let (res, _stats) ← simp rhs0 ctx #[(← Simp.getSimprocs)] none
  let rhs := res.expr
  let proof ← mkEqTrans rwProof (← res.getProof)

  let (rhs, proof) ← recursionToFuel lhs rhs proof

  trace[tactic.rsimp_decide] "Optimized expression:{indentExpr rhs}"
  addDecl <| Declaration.defnDecl { info with
    name := opt_name, type := info.type, value := rhs, levelParams := info.levelParams
  }
  let proof_type ← mkEq lhs (mkConst opt_name (info.levelParams.map mkLevelParam))
  addDecl <| Declaration.thmDecl {
    name := proof_name, type := proof_type, value := proof, levelParams := info.levelParams
  }
  addSimpTheorem se proof_name (post := true) (inv := false) AttributeKind.global (prio := eval_prio default)

/--
TODO
-/
syntax (name := rsimp_optimize) "rsimp_optimize" : attr

initialize registerBuiltinAttribute {
    name  := `rsimp_optimize
    descr := "optimize for kernel reduction"
    add   := fun declName _stx attrKind => do
      unless attrKind == AttributeKind.global do throwError "invalid attribute 'rsimp_optimize', must be global"
      (optimize declName).run' {} {}
  }
