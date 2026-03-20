/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia Markus Himmel
-/
module

prelude
public import Init.Data.ToString.Extra
import all Init.Data.Int.Repr
import Init.Data.Int.Order
import Init.Data.Int.LemmasAux

namespace Int

public theorem repr_eq_if {a : Int} :
    a.repr = if 0 ≤ a then a.toNat.repr else "-" ++ (-a).toNat.repr := by
  cases a <;> simp [Int.repr]

@[simp]
public theorem toString_eq_repr {a : Int} : toString a = a.repr := (rfl)

end Int
