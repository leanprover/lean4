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
  compare x y := compareOfLessAndEq x y

instance : TransOrd String :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    String.le_antisymm String.le_trans String.le_total String.not_le

instance : LawfulEqOrd String where
  eq_of_compare h := compareOfLessAndEq_eq_eq String.le_refl String.not_le |>.mp h

end String

namespace Char

instance : TransOrd Char :=
  TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Char.le_antisymm Char.le_trans Char.le_total Char.not_le

instance : LawfulEqOrd Char where
  eq_of_compare h := compareOfLessAndEq_eq_eq Char.le_refl Char.not_le |>.mp h

end Char
