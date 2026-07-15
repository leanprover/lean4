import Lean
import Std.Tactic.Do

/-!
Several `if`s with a shared continuation. Each `if` makes the do-elaborator emit a `__do_jp` for
its trailing code, so `vcgen +jp` proves each continuation once instead of zeta-unfolding it into
both branches. Without `+jp` the VC count grows exponentially in the number of `if`s.
-/

open Lean Meta Order Std.Internal.Do

namespace IfsJP

set_option mvcgen.warning false

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  let mut x := s
  if x > 0 then x := x + v else x := x + (v + 1)
  if x > 1 then x := x + v else x := x + (v + 1)
  if x > 2 then x := x + v else x := x + (v + 1)
  set x

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ⦃fun _ => True⦄ loop n ⦃fun _ s => 0 < s⦄

end IfsJP
