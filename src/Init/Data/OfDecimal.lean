/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Float
import Init.Data.Nat

/- For decimal numbers (e.g., `1.23`).
   The Lean frontend uses `OfDecimal.ofDecimal 123 2` to represent `1.23` -/
class OfDecimal (α : Type u) where
  ofDecimal : Nat → Nat → α

@[defaultInstance]
instance : OfDecimal Float where
  ofDecimal m e := Float.ofDecimal m e
