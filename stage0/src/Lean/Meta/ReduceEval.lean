/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

/-! Evaluation by reduction -/

import Lean.Meta.Offset

namespace Lean.Meta

class ReduceEval (α : Type) :=
  (reduceEval : Expr → MetaM α)

def reduceEval {α : Type} [ReduceEval α] (e : Expr) : MetaM α :=
  withAtLeastTransparency TransparencyMode.default $
  ReduceEval.reduceEval e

private def throwFailedToEval {α} (e : Expr) : MetaM α :=
  throwError! "reduceEval: failed to evaluate argument{indentExpr e}"

instance : ReduceEval Nat := ⟨fun e => do
  let e ← whnf e
  let some n ← pure $ evalNat e | throwFailedToEval e
  pure n⟩

instance {α : Type} [ReduceEval α] : ReduceEval (Option α) := ⟨fun e => do
  let e ← whnf e
  let Expr.const c .. ← pure e.getAppFn | throwFailedToEval e
  let nargs := e.getAppNumArgs
  if      c == `Option.none && nargs == 0 then pure none
  else if c == `Option.some && nargs == 1 then some <$> reduceEval e.appArg!
  else throwFailedToEval e⟩

instance : ReduceEval String := ⟨fun e => do
  let Expr.lit (Literal.strVal s) _ ← whnf e | throwFailedToEval e
  pure s⟩

private partial def evalName (e : Expr) : MetaM Name := do
  let e ← whnf e
  let Expr.const c _ _ ← pure e.getAppFn | throwFailedToEval e
  let nargs := e.getAppNumArgs
  if      c == `Lean.Name.anonymous && nargs == 0 then pure Name.anonymous
  else if c == `Lean.Name.str && nargs == 3 then do
    let n ← evalName $ e.getArg! 0
    let s ← reduceEval $ e.getArg! 1
    pure $ mkNameStr n s
  else if c == `Lean.Name.num && nargs == 3 then do
    let n ← evalName $ e.getArg! 0
    let u ← reduceEval $ e.getArg! 1
    pure $ mkNameNum n u
  else
    throwFailedToEval e

instance : ReduceEval Name := ⟨evalName⟩

end Lean.Meta
