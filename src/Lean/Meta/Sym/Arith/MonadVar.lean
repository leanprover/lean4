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

/-- Read a variable's Lean expression by index. Used by `DenoteExpr` and diagnostics (PP). -/
class MonadGetVar (m : Type → Type) where
  getVar : Var → m Expr

export MonadGetVar (getVar)

@[always_inline]
instance (m n) [MonadLift m n] [MonadGetVar m] : MonadGetVar n where
  getVar x := liftM (getVar x : m Expr)

/-- Create or lookup a variable for a Lean expression. Used by reification. -/
class MonadMkVar (m : Type → Type) where
  mkVar : Expr → m Var

export MonadMkVar (mkVar)

@[always_inline]
instance (m n) [MonadLift m n] [MonadMkVar m] : MonadMkVar n where
  mkVar e := liftM (mkVar e : m Var)

end Lean.Meta.Sym.Arith
