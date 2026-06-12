/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Types
public section
namespace Lean.Meta.Sym.Arith

class MonadCanon (m : Type → Type) where
  /--
  Canonicalize an expression (types, instances, support arguments).
  In `SymM`, this is `Sym.canon`. In `PP.M` (diagnostics), this is the identity.
  -/
  canonExpr : Expr → m Expr
  /--
  Synthesize an instance, returning `none` on failure.
  In `SymM`, this is `Sym.synthInstance?`. In `PP.M`, this is `Meta.synthInstance?`.
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

end Lean.Meta.Sym.Arith
