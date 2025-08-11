/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Subtype.Order
public import Init.Data.Ord

public instance {α : Type u} [Ord α] {P : α → Prop} : Ord (Subtype P) where
  compare a b := compare a.val b.val
