/-!
Regression test for #16028 and #16029: `grind?` records solver steps (`ring`, `lia`) that make
progress without closing the goal or propagating facts, when the rest of the script needs them.
-/

namespace Ring

open Lean.Grind

variable {α : Type} [Field α]

def pair (a b : α) : α := a + b

def f (a b : α) : α := (a + b - pair a b) / 2

theorem pair_comm (a b : α) : pair a b = pair b a := by grind [pair]

/--
info: Try these:
  [apply] grind only [f, pair_comm]
  [apply] grind =>
    instantiate only [f]
    ring
    instantiate only [pair_comm]
-/
#guard_msgs in
example [IsCharP α 0] (a b : α) : f a b = f b a := by grind? [f, pair_comm]

example [IsCharP α 0] (a b : α) : f a b = f b a := by grind only [f, pair_comm]

end Ring

namespace Lia

def f (n : Nat) : Nat := n

def g (n : Nat) : Nat := f n / 2

/--
info: Try these:
  [apply] grind only [g, f]
  [apply] grind =>
    instantiate only [g]
    lia
    instantiate only [f]
-/
#guard_msgs in
example (n a : Nat) (h : 2 * a = n) : a = g n := by grind? [g, f]

example (n a : Nat) (h : 2 * a = n) : a = g n := by grind only [g, f]

end Lia
