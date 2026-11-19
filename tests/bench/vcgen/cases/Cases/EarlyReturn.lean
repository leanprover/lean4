import Lean
import Std.Tactic.Do

/-!
A `for` loop with an early return and code after the loop. `chain n x` unfolds to `n` nested
`if`s, and the loop body returns on each of their `n` results, so `vcgen` checks `n` returns against
the code after the loop.
-/

open Lean Meta Order Std.WP

set_option experimental.intrinsic true

namespace EarlyReturn

def chain : Nat → Nat → StateM Nat (Option Nat)
  | 0, _ => pure none
  | n+1, x => if x = n then pure (some (n + 1)) else chain n x

def search (n : Nat) (xs : List Nat) : StateM Nat Nat := do
  let mut acc := 0
  for x in xs invariant _ _ _ => True do
    match ← chain n x with
    | some v => return acc + v
    | none => acc := acc + x
  let s ← get
  set (s + acc)
  return acc + s + 1

def Goal (n : Nat) : Prop := ∀ xs, ⦃fun _ => True⦄ search n xs ⦃fun _ _ => True⦄

end EarlyReturn
