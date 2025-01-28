/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Ord

set_option autoImplicit false
set_option linter.missingDocs true

universe u

/-- A typeclasses for ordered types for which `compare a a = .eq` for all `a`. -/
class ReflOrd (α : Type u) [Ord α] : Prop where
  /-- Comparison is reflexive. -/
  compare_self {a : α} : compare a a = .eq

export ReflOrd (compare_self)

attribute [simp] compare_self
