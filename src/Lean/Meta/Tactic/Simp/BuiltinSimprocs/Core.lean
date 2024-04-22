/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Simproc
import Lean.Meta.Tactic.Simp.Simproc

open Lean Meta Simp

builtin_simproc ↓ [simp, seval] reduceIte (ite _ _ _) := fun e => do
  let_expr f@ite α c i tb eb ← e | return .continue
  let r ← simp c
  if r.expr.isTrue then
    let pr    := mkApp (mkApp5 (mkConst ``ite_cond_eq_true f.constLevels!) α c i tb eb) (← r.getProof)
    return .visit { expr := tb, proof? := pr }
  if r.expr.isFalse then
    let pr    := mkApp (mkApp5 (mkConst ``ite_cond_eq_false f.constLevels!) α c i tb eb) (← r.getProof)
    return .visit { expr := eb, proof? := pr }
  return .continue

builtin_simproc ↓ [simp, seval] reduceDite (dite _ _ _) := fun e => do
  let_expr f@dite α c i tb eb ← e | return .continue
  let r ← simp c
  if r.expr.isTrue then
    let pr    ← r.getProof
    let h     := mkApp2 (mkConst ``of_eq_true) c pr
    let eNew  := mkApp tb h |>.headBeta
    let prNew := mkApp (mkApp5 (mkConst ``dite_cond_eq_true f.constLevels!) α c i tb eb) pr
    return .visit { expr := eNew, proof? := prNew }
  if r.expr.isFalse then
    let pr    ← r.getProof
    let h     := mkApp2 (mkConst ``of_eq_false) c pr
    let eNew  := mkApp eb h |>.headBeta
    let prNew := mkApp (mkApp5 (mkConst ``dite_cond_eq_false f.constLevels!) α c i tb eb) pr
    return .visit { expr := eNew, proof? := prNew }
  return .continue
