/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Simproc

open Lean Meta Simp

builtin_simproc ↓ reduceIte (ite _ _ _) := fun e => OptionT.run do
  guard (e.isAppOfArity ``ite 5)
  let c := e.getArg! 1
  let r ← simp c
  if r.expr.isConstOf ``True then
    let eNew  := e.getArg! 3
    let pr    := mkApp (mkAppN (mkConst ``ite_cond_eq_true e.getAppFn.constLevels!) e.getAppArgs) (← r.getProof)
    return .visit { expr := eNew, proof? := pr }
  if r.expr.isConstOf ``False then
    let eNew  := e.getArg! 4
    let pr    := mkApp (mkAppN (mkConst ``ite_cond_eq_false e.getAppFn.constLevels!) e.getAppArgs) (← r.getProof)
    return .visit { expr := eNew, proof? := pr }
  failure

builtin_simproc ↓ reduceDite (dite _ _ _) := fun e => OptionT.run do
  guard (e.isAppOfArity ``dite 5)
  let c := e.getArg! 1
  let r ← simp c
  if r.expr.isConstOf ``True then
    let pr    ← r.getProof
    let h     := mkApp2 (mkConst ``of_eq_true) c pr
    let eNew  := mkApp (e.getArg! 3) h |>.headBeta
    let prNew := mkApp (mkAppN (mkConst ``dite_cond_eq_true e.getAppFn.constLevels!) e.getAppArgs) pr
    return .visit { expr := eNew, proof? := prNew }
  if r.expr.isConstOf ``False then
    let pr    ← r.getProof
    let h     := mkApp2 (mkConst ``of_eq_false) c pr
    let eNew  := mkApp (e.getArg! 4) h |>.headBeta
    let prNew := mkApp (mkAppN (mkConst ``dite_cond_eq_false e.getAppFn.constLevels!) e.getAppArgs) pr
    return .visit { expr := eNew, proof? := prNew }
  failure
