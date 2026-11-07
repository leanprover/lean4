import Lean
import Std.Tactic.Do

/-!
One join point with many jumps. `chain n x` unfolds to `n` nested `if`s, and the continuation of
`wide n` after `chain n x` is a join point that each of the `n` results jumps to, so `vcgen +jp`
disjoins `n` jump payloads in one `?H`.
-/

open Lean Meta Order Std.WP

namespace WideJP

def chain : Nat → Nat → StateM Nat Nat
  | 0, _ => pure 1
  | n+1, x => if x = n then pure (n + 2) else chain n x

def wide (n : Nat) : StateM Nat Nat := do
  let x ← get
  let mut y := 0
  if x < n then y ← chain n x
  return y + 1

def Goal (n : Nat) : Prop := ⦃fun _ => True⦄ wide n ⦃fun r _ => 0 < r⦄

end WideJP
