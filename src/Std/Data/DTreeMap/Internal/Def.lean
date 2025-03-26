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

variable {α : Type u} {β : α → Type v}

namespace Impl

/-!
## `size`

In contrast to other functions, `size` is defined here because it is required to define the
`Balanced` predicate (see `Std.Data.DTreeMap.Internal.Balanced`).
-/

/-- The size information stored in the tree. -/
@[inline]
def size : Impl α β → Nat
  | inner sz _ _ _ _ => sz
  | leaf => 0

@[Std.Internal.tree_tac] theorem size_leaf : (Impl.leaf : Impl α β).size = 0 := rfl
@[Std.Internal.tree_tac] theorem size_inner {sz k v l r} : (Impl.inner sz k v l r : Impl α β).size = sz := rfl

/-!
## `toListModel`

`toListModel` is defined here because it is required to define the `Ordered` predicate.
-/

/--
Flattens a tree into a list of key-value pairs. This function is defined for verification
purposes and should not be executed because it is very inefficient.
-/
def toListModel : Impl α β → List ((a : α) × β a)
  | .leaf => []
  | .inner _ k v l r => l.toListModel ++ ⟨k, v⟩ :: r.toListModel

@[simp] theorem toListModel_leaf : (.leaf : Impl α β).toListModel = [] := rfl
@[simp] theorem toListModel_inner {sz k v l r} :
  (.inner sz k v l r : Impl α β).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := rfl

end Std.DTreeMap.Internal.Impl
