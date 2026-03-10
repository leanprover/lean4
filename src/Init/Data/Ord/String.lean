/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
module

prelude
public import Init.Data.Order.Ord
public import Init.Data.String.Basic
import Init.Data.Char.Lemmas
import Init.Data.String.Lemmas

public section

/-!
# Instances for strings.

-/

set_option autoImplicit false
set_option linter.missingDocs true

open Std

namespace String

instance : Ord String where
  compare x y := compareOfLT x y

instance : TransOrd String := transCmp_compareOfLT { asymm _ _ := String.lt_asymm }
  { trans {_ _ _} := by simpa only [String.not_lt] using flip String.le_trans }

instance : LawfulEqOrd String where
  eq_of_compare h := compareOfLT_eq_eq { asymm _ _ := String.lt_asymm }
    { trichotomous _ _ h₁ h₂ := String.le_antisymm (String.not_lt.mp h₂) (String.not_lt.mp h₁) } |>.mp h

end String

namespace Char

instance : TransOrd Char := transCmp_compareOfLT { asymm _ _ := Char.lt_asymm }
  { trans {_ _ _} := by simpa only [Char.not_lt] using flip Char.le_trans }

instance : LawfulEqOrd Char where
  eq_of_compare h := compareOfLT_eq_eq { asymm _ _ := Char.lt_asymm } |>.mp h

end Char
