/-!
Tests that the homomorphism extension asserts ground evaluation steps with a proof whose type is
the asserted equality. Ground evaluation proves `3 * 2 = 6` over `Rat` by `Eq.refl 6`, which only
type checks at default transparency, and `grind.debug` used to report an internal error.
See #15867.
-/

set_option grind.debug true

example : (3 : Rat) * 2 = 6 := by
  grind

example : (3 : Rat) + 2 = 5 := by
  grind

example : (3 : Rat) - 2 = 1 := by
  grind

example : (6 : Rat) / 2 = 3 := by
  grind

example (x : Rat) (h : x = 3 * 2) : x = 6 := by
  grind
