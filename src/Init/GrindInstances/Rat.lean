/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude

public import Init.Grind.Ordered.Module
public import Init.Grind.Ring.Basic
public import Init.Data.Rat.Lemmas

public section

namespace Lean.Grind

instance : AddCommMonoid Rat where
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc

instance : AddCommGroup Rat where
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg

end Lean.Grind
