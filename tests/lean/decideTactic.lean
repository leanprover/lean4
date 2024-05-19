/-!
# Tests of the `decide` tactic
-/

/-!
Success
-/
example : 2 + 2 ≠ 5 := by decide

/-!
False proposition
-/
example : 1 ≠ 1 := by decide

/-!
Irreducible decidable instance
-/
opaque unknownProp : Prop

open scoped Classical in
example : unknownProp := by decide
