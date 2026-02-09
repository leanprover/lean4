/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ring.Field
public import Init.Data.OfScientific

public section

namespace Lean.Grind

attribute [local instance] Semiring.natCast

/--
A type class that ensures that `OfScientific.ofScientific` is properly defined with respect to
the field structure.
-/
class LawfulOfScientific (α : Type u) [Field α] [OfScientific α] : Prop where
  /--
  `OfScientific.ofScientific` is properly defined with respect to the field structure.
  -/
  ofScientific_def :
    OfScientific.ofScientific m s e = if s then (Nat.cast m : α) / 10^e else (Nat.cast m : α) * 10^e

end Lean.Grind
