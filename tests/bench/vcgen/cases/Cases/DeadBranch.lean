import Lean
import Std.WP

/-!
Branches on a value that the state determines. `step i` sets the state to `i` and then tests
whether the state is `i`, so the `else` branch is dead. The split leaves the hypothesis `¬i = i`
on the `else` path, which ground evaluation rewrites to `False`, so `vcgen` closes the path at the
split. With `vcgen -simp`, both paths of every split continue, and the `n` steps produce `2 ^ n`
paths.
-/

open Lean Meta Order Std.WP

namespace DeadBranch

set_option experimental.vcgen true

abbrev M := StateM Nat

def step (i : Nat) : M Unit := do
  set i
  let pc ← get
  if pc = i then pure () else set (i + 1)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ⦃fun _ => True⦄ loop n ⦃fun _ s => s = 0⦄

end DeadBranch
