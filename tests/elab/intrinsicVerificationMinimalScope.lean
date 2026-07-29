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

/-! A missing clause defaults to `⊤`, whose notation the theorem activates along with the
instances. Without the notation in scope here, the statement prints the constant it denotes. -/

def onlyEnsures (n : Nat) : Id Nat
    ensures r => r = n
  := pure n

/-- info: onlyEnsures.spec : ∀ (n : Nat), ⦃ Lean.Order.top ⦄ onlyEnsures n ⦃ fun r => r = n ⦄ -/
#guard_msgs in
#check @onlyEnsures.spec

def onlyRequire (n : Nat) : Id Nat
    require 0 ≤ n
  := pure n

/-- info: onlyRequire.spec : ∀ (n : Nat), ⦃ 0 ≤ n ⦄ onlyRequire n ⦃ fun x => Lean.Order.top ⦄ -/
#guard_msgs in
#check @onlyRequire.spec
