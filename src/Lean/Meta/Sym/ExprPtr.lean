/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Expr
public section
namespace Lean.Meta.Sym

@[inline] def isSameExpr (a b : Expr) : Bool :=
  -- It is safe to use pointer equality because we hashcons all expressions
  -- inserted into the E-graph
  unsafe ptrEq a b

/--
Key for the `ENodeMap`, `ParentMap`, and other maps and sets.
We use pointer addresses and rely on the fact all internalized expressions
have been hash-consed, i.e., we have applied `shareCommon`.
-/
structure ExprPtr where
  expr : Expr

abbrev hashPtrExpr (e : Expr) : UInt64 :=
  unsafe (ptrAddrUnsafe e >>> 3).toUInt64

instance : Hashable ExprPtr where
  hash k := hashPtrExpr k.expr

instance : BEq ExprPtr where
  beq k₁ k₂ := isSameExpr k₁.expr k₂.expr

end Lean.Meta.Sym
