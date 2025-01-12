/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr

namespace Lean.Meta.Grind

@[inline] def isSameExpr (a b : Expr) : Bool :=
  -- It is safe to use pointer equality because we hashcons all expressions
  -- inserted into the E-graph
  unsafe ptrEq a b

/--
Key for the `ENodeMap` and `ParentMap` map.
We use pointer addresses and rely on the fact all internalized expressions
have been hash-consed, i.e., we have applied `shareCommon`.
-/
structure ENodeKey where
  expr : Expr

instance : Hashable ENodeKey where
  hash k := unsafe (ptrAddrUnsafe k.expr).toUInt64

instance : BEq ENodeKey where
  beq k₁ k₂ := isSameExpr k₁.expr k₂.expr

end Lean.Meta.Grind
