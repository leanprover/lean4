/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Meta.Offset

public section

/-! Evaluation by reduction -/

namespace Lean.Meta

class ReduceEval (α : Type) where
  reduceEval : Expr → MetaM α

def reduceEval [ReduceEval α] (e : Expr) : MetaM α :=
  withAtLeastTransparency TransparencyMode.default $
  ReduceEval.reduceEval e

private def throwFailedToEval (e : Expr) : MetaM α :=
  throwError "reduceEval: failed to evaluate argument{indentExpr e}"

instance : ReduceEval Nat where
  reduceEval e := private do
    let e ← whnf e
    let some n ← evalNat e | throwFailedToEval e
    pure n

instance [ReduceEval α] : ReduceEval (Option α) where
  reduceEval e := private do
    let e ← whnf e
    let Expr.const c .. ← pure e.getAppFn | throwFailedToEval e
    let nargs := e.getAppNumArgs
    if      c == ``Option.none && nargs == 0 then pure none
    else if c == ``Option.some && nargs == 1 then some <$> reduceEval e.appArg!
    else throwFailedToEval e

instance : ReduceEval String where
  reduceEval e := private do
    let Expr.lit (Literal.strVal s) ← whnf e | throwFailedToEval e
    pure s

private partial def evalName (e : Expr) : MetaM Name := do
  let e ← whnf e
  let Expr.const c _ ← pure e.getAppFn | throwFailedToEval e
  let nargs := e.getAppNumArgs
  if      c == ``Lean.Name.anonymous && nargs == 0 then pure Name.anonymous
  else if c == ``Lean.Name.str && nargs == 2 then do
    let n ← evalName $ e.getArg! 0
    let s ← reduceEval $ e.getArg! 1
    pure $ Name.mkStr n s
  else if c == ``Lean.Name.num && nargs == 2 then do
    let n ← evalName $ e.getArg! 0
    let u ← reduceEval $ e.getArg! 1
    pure $ Name.mkNum n u
  else
    throwFailedToEval e

instance : ReduceEval Name where
  reduceEval := private evalName

private partial def evalList [ReduceEval α] (e : Expr) : MetaM (List α) := do
  let e ← whnf e
  let .const c _ := e.getAppFn | throwFailedToEval e
  let nargs := e.getAppNumArgs
  match c, nargs with
    | ``List.nil, 1 => pure []
    | ``List.cons, 3 => return (← reduceEval (e.getArg! 1)) :: (← evalList (e.getArg! 2))
    | _, _ => throwFailedToEval e

instance [ReduceEval α] : ReduceEval (List α) where
  reduceEval := private evalList

instance [NeZero n] : ReduceEval (Fin n) where
  reduceEval := private fun e => do
    let e ← whnf e
    if e.isAppOfArity ``Fin.mk 3 then
      return Fin.ofNat _ (← reduceEval (e.getArg! 1))
    else
      throwFailedToEval e

instance {n : Nat} : ReduceEval (BitVec n) where
  reduceEval := private fun e => do
    let e ← whnf e
    if e.isAppOfArity ``BitVec.ofFin 2 then
      have : 2^n - 1 + 1 = 2^n := Nat.sub_one_add_one_eq_of_pos (Nat.two_pow_pos n)
      let _ : ReduceEval (Fin (2^n)) := this ▸ (inferInstanceAs <| ReduceEval (Fin (2^n - 1 + 1)))
      pure ⟨(← reduceEval (e.getArg! 1))⟩
    else
      throwFailedToEval e

instance : ReduceEval Bool where
  reduceEval := private fun e => do
    let e ← whnf e
    if e.isAppOf ``true then
      pure true
    else if e.isAppOf ``false then
      pure false
    else
      throwFailedToEval e

instance : ReduceEval BinderInfo where
  reduceEval := private fun e => do
    match (← whnf e).constName? with
    | some ``BinderInfo.default => pure .default
    | some ``BinderInfo.implicit => pure .implicit
    | some ``BinderInfo.strictImplicit => pure .strictImplicit
    | some ``BinderInfo.instImplicit => pure .instImplicit
    | _ => throwFailedToEval e

instance : ReduceEval Literal where
  reduceEval := private fun e => do
    let e ← whnf e
    if e.isAppOfArity ``Literal.natVal 1 then
      return .natVal (← reduceEval (e.getArg! 0))
    else if e.isAppOfArity ``Literal.strVal 1 then
      return .strVal (← reduceEval (e.getArg! 0))
    else
      throwFailedToEval e

instance : ReduceEval MVarId where
  reduceEval e := private do
    let e ← whnf e
    if e.isAppOfArity ``MVarId.mk 1 then
      return ⟨← reduceEval (e.getArg! 0)⟩
    else
      throwFailedToEval e

instance : ReduceEval LevelMVarId where
  reduceEval e := private do
    let e ← whnf e
    if e.isAppOfArity ``LevelMVarId.mk 1 then
      return ⟨← reduceEval (e.getArg! 0)⟩
    else
      throwFailedToEval e

instance : ReduceEval FVarId where
  reduceEval e := private do
    let e ← whnf e
    if e.isAppOfArity ``FVarId.mk 1 then
      return ⟨← reduceEval (e.getArg! 0)⟩
    else
      throwFailedToEval e


end Lean.Meta
