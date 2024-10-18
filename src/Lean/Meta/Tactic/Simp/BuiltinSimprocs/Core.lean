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

builtin_simproc ↓ [simp, seval] reduceDIte (dite _ _ _) := fun e => do
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

builtin_dsimproc ↓ [simp, seval] dreduceIte (ite _ _ _) := fun e => do
  unless (← inDSimp) do
    -- If `simp` is not in `dsimp` mode, we should use `reduceIte`
    return .continue
  let_expr ite _ c i tb eb ← e | return .continue
  /-
  We don't want to use `whnfD i` directly because it is potentially too expensive.
  We considered using `whnfI i`, but it is too inconvenient for users.
  They would have to list auxiliary functions used to establish that a proposition
  is decidable as `reducible` and/or list them to be unfolded by `simp`.
  Thus, we are currently using the following "filter": if `simp` reduces the
  condition to `True` or `False`, we execute `whnfD i` and check whether it
  reduces `i` to `Decidable.isTrue` or `Decidable.isFalse`.
  Recall that all declarations defined by well-founded recursion are
  now marked as `[irreducible]`. Thus, we will not timeout trying to
  reduce them using the default reduction mode.
  -/
  let r ← simp c
  if r.expr.isTrue || r.expr.isFalse then
    match_expr (← whnfD i) with
    | Decidable.isTrue _ _ => return .visit tb
    | Decidable.isFalse _ _ => return .visit eb
    | _ => return .continue
  return .continue

builtin_dsimproc ↓ [simp, seval] dreduceDIte (dite _ _ _) := fun e => do
  unless (← inDSimp) do
    -- If `simp` is not in `dsimp` mode, we should use `reduceDIte`
    return .continue
  let_expr dite _ c i tb eb ← e | return .continue
  -- See comment at `dreduceIte`
  let r ← simp c
  if r.expr.isTrue || r.expr.isFalse then
    match_expr (← whnfD i) with
    | Decidable.isTrue _ h => return .visit (mkApp tb h).headBeta
    | Decidable.isFalse _ h => return .visit (mkApp eb h).headBeta
    | _ => return .continue
  return .continue

builtin_simproc [simp, seval] reduceCtorEq (_ = _) := fun e => withReducibleAndInstances do
  let_expr Eq _ lhs rhs ← e | return .continue
  match (← constructorApp'? lhs), (← constructorApp'? rhs) with
  | some (c₁, _), some (c₂, _) =>
    if c₁.name != c₂.name then
      withLocalDeclD `h e fun h =>
        return .done { expr := mkConst ``False, proof? := (← withDefault <| mkEqFalse' (← mkLambdaFVars #[h] (← mkNoConfusion (mkConst ``False) h))) }
    else
      return .continue
  | _, _ => return .continue
