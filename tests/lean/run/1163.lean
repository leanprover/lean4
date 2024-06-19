import Lean
open Lean Elab Tactic

macro "obviously1" : tactic => `(tactic| exact sorryAx _)

theorem result1 : False := by obviously1

elab "obviously2" : tactic =>
  liftMetaTactic1 fun mvarId => mvarId.admit *> pure none

theorem result2 : False := by obviously2

/--
error: failed to synthesize
  OfNat Bool 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Bool
due to the absence of the instance above
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
def x : Bool := 0

theorem result3 : False := by obviously2

/--
error: failed to synthesize
  OfNat Bool 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Bool
due to the absence of the instance above
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
theorem result4 : False := by -- Does not generate a `sorry` warning because there is an error
  let x : Bool := 0
  obviously2
