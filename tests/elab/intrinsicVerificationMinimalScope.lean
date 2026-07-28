import Std.Internal.Do

/-! A `def` contract elaborates with only `Std.Internal.Do` imported and without any `open`:
the generated spec theorem activates the scoped instances it needs by itself. -/

set_option mvcgen.warning false

def clampLow (n lo : Nat) : Id Nat
    require lo ≤ n
    ensures r => r = n
  := pure n

/-- info: clampLow.spec : ∀ (n lo : Nat), ⦃ lo ≤ n ⦄ clampLow n lo ⦃ fun r => r = n ⦄ -/
#guard_msgs in
#check @clampLow.spec
