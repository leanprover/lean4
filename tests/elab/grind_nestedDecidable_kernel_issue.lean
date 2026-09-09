module
set_option warn.sorry false
/-!
Paul Reichert's examples: `grind` + kernel interaction through `Grind.nestedDecidable`.

`grind` canonicalizes `Decidable` instances under the identity wrapper
`Grind.nestedDecidable`, assuming `X =?= nestedDecidable X` is free. The elaborator
unfolds the reducible wrapper instantly, but the kernel does not take `[reducible]` hint.
We fix the issue by tagging `Grind.nestedDecidable` as an abbreviation which tags in the
kernel as an abbreviation.
-/

set_option maxHeartbeats 1000 -- for the health of your machines

/-!

Grind's literal normalization produces `97 ≤ c.val + 4294967264` and cutsat closes the goal,
but `decide_eq_true_eq`'s metavariable type check
```lean
Decidable (97 ≤ c.val + 4294967264) =?= Decidable ('a'.val ≤ {val := c.val + ('A'.val - 'a'.val), ...}.val)
```
fails at implicit transparency because we made `UInt32.toBitVec` semireducible.
Grind then keeps the `decide` layer, canonicalizes instances under `Grind.nestedDecidable`,
and leaves it to the kernel to verify that `X =?= nestedDecidable X` is true with
`X = 'a'.val.decLe (c.val + ('A'.val - 'a'.val))`.
This leads to the exact problem shown previously.
-/

section
set_option allowUnsafeReducibility true
attribute [local semireducible] UInt32.toBitVec -- or `Char.ofNat`

set_option maxHeartbeats 5000 in
example (c : Char) : c.toUpper.isLower = false := by
  simp only [Char.isLower, Char.toUpper]
  split
  · grind only  -- (kernel) deterministic timeout
  · sorry

end
