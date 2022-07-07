/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Meta.Offset

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
  reduceEval e := do
    let e ← whnf e
    let some n ← evalNat e | throwFailedToEval e
    pure n

instance [ReduceEval α] : ReduceEval (Option α) where
  reduceEval e := do
    let e ← whnf e
    let Expr.const c .. ← pure e.getAppFn | throwFailedToEval e
    let nargs := e.getAppNumArgs
    if      c == ``Option.none && nargs == 0 then pure none
    else if c == ``Option.some && nargs == 1 then some <$> reduceEval e.appArg!
    else throwFailedToEval e

instance : ReduceEval String where
  reduceEval e := do
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
  reduceEval := evalName

end Lean.Meta
