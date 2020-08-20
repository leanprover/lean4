/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

/-! Evaluation by reduction -/

import Lean.Meta.Offset

namespace Lean
namespace Meta

class HasReduceEval (α : Type) :=
(reduceEval : Expr → MetaM α)

def reduceEval {α : Type} [HasReduceEval α] (e : Expr) : MetaM α :=
withAtLeastTransparency TransparencyMode.default $
HasReduceEval.reduceEval e

instance Nat.hasReduceEval : HasReduceEval Nat := ⟨fun e => do
e ← whnf e;
some n ← pure $ evalNat e
  | throwError $ "reduceEval: failed to evaluate argument: " ++ toString e;
pure n⟩

instance Option.hasReduceEval {α : Type} [HasReduceEval α] : HasReduceEval (Option α) := ⟨fun e => do
e ← whnf e;
Expr.const c _ _ ← pure e.getAppFn
  | throwError $ "reduceEval: failed to evaluate argument: " ++ toString e;
let nargs := e.getAppNumArgs;
if      c == `Option.none && nargs == 0 then pure none
else if c == `Option.some && nargs == 1 then some <$> reduceEval e.appArg!
else throwError $ "reduceEval: failed to evaluate argument: " ++ toString e⟩

instance String.hasReduceEval : HasReduceEval String := ⟨fun e => do
Expr.lit (Literal.strVal s) _ ← whnf e
  | throwError $ "reduceEval: failed to evaluate argument: " ++ toString e;
pure s⟩

private partial def evalName : Expr → MetaM Name | e => do
e ← whnf e;
Expr.const c _ _ ← pure e.getAppFn
  | throwError $ "reduceEval: failed to evaluate argument: " ++ toString e;
let nargs := e.getAppNumArgs;
if      c == `Lean.Name.anonymous && nargs == 0 then pure Name.anonymous
else if c == `Lean.Name.str && nargs == 3 then do
  n ← evalName $ e.getArg! 0;
  s ← reduceEval $ e.getArg! 1;
  pure $ mkNameStr n s
else if c == `Lean.Name.num && nargs == 3 then do
  n ← evalName $ e.getArg! 0;
  u ← reduceEval $ e.getArg! 1;
  pure $ mkNameNum n u
else
  throwError $ "reduceEval: failed to evaluate argument: " ++ toString e

instance Name.hasReduceEval : HasReduceEval Name := ⟨evalName⟩

end Meta
end Lean
