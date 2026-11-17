import Std.WP

set_option experimental.vcgen true
open Std.WP

/-!
`vcgen +jp [f]` unfolds the definition `f` through a spec made from its unfold equation. The
right-hand side of that equation is the whole program, with one `have __do_jp := …` per join point.
Making the spec keeps the join points, so its cost is linear in the number of `if`s.
-/

def chain (c : Nat → Bool) : StateM Nat Unit := do
  let mut x ← get
  if c 0 then x := x + 0 else x := x + (0 + 1)
  if c 1 then x := x + 0 else x := x + (0 + 1)
  if c 2 then x := x + 0 else x := x + (0 + 1)
  if c 3 then x := x + 0 else x := x + (0 + 1)
  if c 4 then x := x + 0 else x := x + (0 + 1)
  if c 5 then x := x + 0 else x := x + (0 + 1)
  if c 6 then x := x + 0 else x := x + (0 + 1)
  if c 7 then x := x + 0 else x := x + (0 + 1)
  if c 8 then x := x + 0 else x := x + (0 + 1)
  if c 9 then x := x + 0 else x := x + (0 + 1)
  if c 10 then x := x + 0 else x := x + (0 + 1)
  if c 11 then x := x + 0 else x := x + (0 + 1)
  if c 12 then x := x + 0 else x := x + (0 + 1)
  if c 13 then x := x + 0 else x := x + (0 + 1)
  if c 14 then x := x + 0 else x := x + (0 + 1)
  if c 15 then x := x + 0 else x := x + (0 + 1)
  set x

set_option maxHeartbeats 20000 in
example : ⦃fun s => s = s₀⦄ chain c ⦃fun _ s => s₀ ≤ s⦄ := by
  vcgen +jp [chain] with finish
