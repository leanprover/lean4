/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Nat.Bitwise
import Init.Data.Fin.Basic

namespace Fin

@[simp] theorem and_val (a b : Fin n) : (a &&& b).val = a.val &&& b.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)

end Fin
