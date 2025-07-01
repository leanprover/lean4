import Init.Data.Range.Polymorphic
import Std.Data.Iterators

open Std.Iterators

/-- info: true -/
#guard_msgs in
#eval "b" ∈ ("a"...="c")

/-- info: [1, 2, 3, 4] -/
#guard_msgs in
#eval (1...=4).toList

/-- info: [2, 3] -/
#guard_msgs in
#eval (1<...4).toList

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval (1...4).toList

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval (1...<4).toList

/-- info: [0, 1, 2, 3, 4] -/
#guard_msgs in
#eval (*...=4).toList

/-- info: 2 -/
#guard_msgs in
#eval (1<...4).size

/-- info: true -/
#guard_msgs in
#eval (1...<1).isEmpty

/-- info: [3, 5, 7, 9, 11, 13] -/
#guard_msgs in
#eval (2<...<15).iter.stepSize 2 |>.toList

/-- info: true -/
#guard_msgs in
#eval 1 ∈ (1...=5)

def g (xs : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for h : i in *...<xs.size do
    sum := sum + xs[i]
  return sum

/-- info: 6 -/
#guard_msgs in
#eval g #[1, 2, 3]

def h (n : Nat) : IO Unit := do
  for i in *...n, j in 2...* do
    IO.println s!"i={i}, j={j}"

/--
info: i=0, j=2
i=1, j=3
i=2, j=4
i=3, j=5
i=4, j=6
-/
#guard_msgs in
#eval h 5
