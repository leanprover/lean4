/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Classes.Ord

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v

namespace Std.DTreeMap.Internal

/-- (Implementation detail) The actual inductive type for the size-balanced tree data structure. -/
inductive Impl (α : Type u) (β : α → Type v) where
  /-- (Implementation detail) -/
  | inner (size : Nat) (k : α) (v : β k) (l r : Impl α β)
  /-- (Implementation detail) -/
  | leaf
deriving Inhabited

/-- The "delta" parameter of the size-bounded tree. Controls how imbalanced the tree can be. -/
@[inline, Std.Internal.tree_tac]
def delta : Nat := 3

/-- The "ratio" parameter of the size-bounded tree. Controls how aggressive the rebalancing
operations are. -/
@[inline, Std.Internal.tree_tac]
def ratio : Nat := 2
