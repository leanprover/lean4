/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Char.Basic
import Init.Data.Char.Lemmas
public import Init.Data.Order.Classes
import Init.Data.Order.Factories
import Init.PropLemmas

open Std

namespace Char

public instance instIsLinearOrder : IsLinearOrder Char := by
  apply IsLinearOrder.of_le
  case le_antisymm => constructor; apply Char.le_antisymm
  case le_trans => constructor; apply Char.le_trans
  case le_total => constructor; apply Char.le_total

public instance : LawfulOrderLT Char where
  lt_iff a b := by
    simp [← Char.not_le, Decidable.imp_iff_not_or, Std.Total.total]

end Char
