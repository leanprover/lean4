import Std.Tactic.Do
import Std.Do.WP.Basic

def tst (n : Nat) : Vector Bool n := Id.run do
  let mut res : Vector Bool n := .ofFn fun _ ↦ false
  for i in [:n] do
    for j in [:n] do
      if i = j ∧ i % 2 = 0 then
        res := res.set! i true
  return res

set_option warn.sorry false in
open Std.Do in
example (n i : Nat) (h : i < n) : (tst n)[i] = (i % 2 == 0) := by
  generalize h : tst n = bs
  apply Std.Do.Id.of_wp_run_eq h
  mvcgen
  -- We should see `inv1` and `inv2` here as separate goals.
  -- `inv2` should not have been spuriously instantiated in terms of `inv1`.
  -- Used to happen because `inv2` was born natural and got instantiated in a .rfl test.
  case inv1 => sorry
  case inv2 => sorry
  all_goals sorry
