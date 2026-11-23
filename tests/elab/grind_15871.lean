/-!
Tests that merging two equivalence classes preserves the congruence root of the new root when the
new root is also a parent of the old root. Here `p = false ∨ q = false` becomes congruent to
`p = false ∨ (p = false ∨ q = false)` when it is merged with `q = false`, and its `congr` field
used to be overwritten with a stale value, violating the `grind.debug` invariant in `checkEqc`.
See #15871.
-/

set_option grind.debug true

example (p q : Bool) : (p && p && q) = (p && q) := by
  grind

example (p q : Prop) : (p ∧ p ∧ q) = (p ∧ q) := by
  grind
