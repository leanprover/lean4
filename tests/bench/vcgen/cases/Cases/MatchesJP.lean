import Lean
import Std.Tactic.Do

/-!
Several `match`es with a shared continuation, the matcher analogue of `IfsJP`. Each `match` makes the
do-elaborator emit a `__do_jp` for its trailing code, so `vcgen +jp` proves each continuation once
instead of zeta-unfolding it into every alternative. Exercises `+jp` on matcher-shaped join points
(genuine `rwMatcher` discharge), where `IfsJP` exercises only `ite`.
-/

open Lean Meta Order Std.Internal.Do

namespace MatchesJP

set_option mvcgen.warning false

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  let mut x := s
  match x with
  | 0 => x := x + v
  | 1 => x := x + (v + 1)
  | _ => x := x + (v + 2)
  match x with
  | 0 => x := x + v
  | 1 => x := x + (v + 1)
  | _ => x := x + (v + 2)
  match x with
  | 0 => x := x + v
  | 1 => x := x + (v + 1)
  | _ => x := x + (v + 2)
  set x

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ⦃fun _ => True⦄ loop n ⦃fun _ s => 0 < s⦄

end MatchesJP
