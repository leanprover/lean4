/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia Markus Himmel
-/
module

prelude
public import Init.Data.ToString.Extra
import Init.Data.Int.Order
import Init.Data.Int.LemmasAux

namespace Int

public theorem toString_eq_if {a : Int} :
    toString a= if 0 ≤ a then a.toNat.repr else "-" ++ (-a).toNat.repr := by
  cases a <;> simp [toString]

end Int
