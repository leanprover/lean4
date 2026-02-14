/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Ring.Types
public import Lean.Exception
public section
namespace Lean.Meta.Sym.Arith.Ring

class MonadCanon (m : Type → Type) where
  /--
  Canonicalize an expression (e.g., hash-cons via `shareCommon`).
  In `SymM`-based monads, this is typically `shareCommon (← canon e)`.
  -/
  canonExpr : Expr → m Expr
  /--
  Synthesize a type class instance, returning `none` on failure.
  -/
  synthInstance? : Expr → m (Option Expr)

export MonadCanon (canonExpr)

@[always_inline]
instance (m n) [MonadLift m n] [MonadCanon m] : MonadCanon n where
  canonExpr e := liftM (canonExpr e : m Expr)
  synthInstance? e := liftM (MonadCanon.synthInstance? e : m (Option Expr))

def MonadCanon.synthInstance [Monad m] [MonadError m] [MonadCanon m] (type : Expr) : m Expr := do
  let some inst ← synthInstance? type
    | throwError "failed to find instance{indentExpr type}"
  return inst

end Lean.Meta.Sym.Arith.Ring
