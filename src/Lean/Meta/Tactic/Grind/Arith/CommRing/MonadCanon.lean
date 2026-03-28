/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
public section
namespace Lean.Meta.Grind.Arith.CommRing

class MonadCanon (m : Type → Type) where
  /--
  Helper function for removing dependency on `GoalM`.
  In `RingM` and `SemiringM`, this is just `sharedCommon (← canon e)`
  When printing counterexamples, we are at `MetaM`, and this is just the identity function.
  -/
  canonExpr : Expr → m Expr
  /--
  Helper function for removing dependency on `GoalM`. During search we
  want to track the instances synthesized by `grind`, and this is `Grind.synthInstance`.
  -/
  synthInstance? : Expr → m (Option Expr)

export MonadCanon (canonExpr)

@[always_inline]
instance (m n) [MonadLift m n] [MonadCanon m] : MonadCanon n where
  canonExpr e := liftM (canonExpr e : m Expr)
  synthInstance? e := liftM (MonadCanon.synthInstance? e : m (Option Expr))

def MonadCanon.synthInstance [Monad m] [MonadError m] [MonadCanon m] (type : Expr) : m Expr := do
  let some inst ← synthInstance? type
    | throwError "`grind` failed to find instance{indentExpr type}"
  return inst

end Lean.Meta.Grind.Arith.CommRing
