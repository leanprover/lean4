import Std.Data.Iterators
import Lean

/-!
Tests for the precedence of the polymorphic range notations `a...b`, `a<...=b`, `*...b`, `a...*`,
etc. (#12055). The notations bind looser than arithmetic operators such as `+` and `*` but tighter
than relations such as `=` and `∈`, and `|>.` applies to the whole range rather than to its upper
bound.
-/

/-! `|>.` applies to the range, not to its upper bound, for all forms of the notation. -/

/-- info: [1, 2] -/
#guard_msgs in
#eval 1...3 |>.toList

/-- info: [1, 2] -/
#guard_msgs in
#eval 1...<3 |>.toList

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval 1...=3 |>.toList

/-- info: [2] -/
#guard_msgs in
#eval 1<...3 |>.toList

/-- info: [2] -/
#guard_msgs in
#eval 1<...<3 |>.toList

/-- info: [2, 3] -/
#guard_msgs in
#eval 1<...=3 |>.toList

/-- info: [0, 1, 2] -/
#guard_msgs in
#eval *...3 |>.toList

/-- info: [0, 1, 2] -/
#guard_msgs in
#eval *...<3 |>.toList

/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval *...=3 |>.toList

/-- info: [254, 255] -/
#guard_msgs in
#eval (254 : UInt8)...* |>.toList

/-- info: [255] -/
#guard_msgs in
#eval (254 : UInt8)<...* |>.toList

/-- info: 256 -/
#guard_msgs in
#eval (*...* : Std.Rii UInt8) |>.toList |>.length

/-- info: 2 -/
#guard_msgs in
#eval 1...3 |>.toList |>.length

/-! Arithmetic operators bind tighter than the range notations, on both sides. -/

/-- info: 1 + 2...3 * 4 : Std.Rco Nat -/
#guard_msgs in
#check 1 + 2...3 * 4

/-- info: [3, 4, 5, 6, 7, 8, 9, 10, 11] -/
#guard_msgs in
#eval 1 + 2...3 * 4 |>.toList

/-- info: [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] -/
#guard_msgs in
#eval 1 + 2...=3 * 4 |>.toList

/-- info: [4, 5, 6, 7, 8, 9, 10, 11] -/
#guard_msgs in
#eval 1 + 2<...3 * 4 |>.toList

/-- info: [0, 1, 2] -/
#guard_msgs in
#eval *...1 + 2 |>.toList

/-- info: [254, 255] -/
#guard_msgs in
#eval (250 : UInt8) + 4...* |>.toList

/-- info: [255] -/
#guard_msgs in
#eval (250 : UInt8) + 4<...* |>.toList

/-- info: -1...1 : Std.Rco Int -/
#guard_msgs in
#check -1...1

/-- info: [-1, 0] -/
#guard_msgs in
#eval -1...1 |>.toList

/-- info: [-2] -/
#guard_msgs in
#eval (-2 : Int)...-1 |>.toList

/-- info: [3, 4, 5] -/
#guard_msgs in
#eval 2 ^ 2 - 1...=5 |>.toList

/-! Function application binds tighter than the range notations. -/

/-- info: Nat.succ 1...Nat.succ 3 : Std.Rco Nat -/
#guard_msgs in
#check Nat.succ 1...Nat.succ 3

/-- info: [2, 3] -/
#guard_msgs in
#eval Nat.succ 1...Nat.succ 3 |>.toList

/-- info: Nat.succ 1...Nat.succ 3 : Std.Rco Nat -/
#guard_msgs in
#check (Nat.succ 1)...(Nat.succ 3)

/-- info: Nat.succ 1<...=Nat.succ 3 : Std.Roc Nat -/
#guard_msgs in
#check (Nat.succ 1)<...=(Nat.succ 3)

/-- info: Nat.succ 1...* : Std.Rci Nat -/
#guard_msgs in
#check (Nat.succ 1)...*

/-- info: *...Nat.succ 3 : Std.Rio Nat -/
#guard_msgs in
#check *...(Nat.succ 3)

/-!
The forms without a lower bound have no left operand, so they can be used as function arguments
without parentheses.
-/

/-- info: [0, 1, 2] -/
#guard_msgs in
#eval id *...3 |>.toList

/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval id *...=3 |>.toList

/-- info: 256 -/
#guard_msgs in
#eval (id *...* : Std.Rii UInt8).toList.length

/-! Relations bind looser than the range notations. -/

/-- info: 2 ∈ 1...3 : Prop -/
#guard_msgs in
#check 2 ∈ 1...3

/-- info: true -/
#guard_msgs in
#eval 2 ∈ 1...3

/-- info: true -/
#guard_msgs in
#eval 2 ∈ 1 + 1...3

/-- info: 1...3 = 1...3 : Prop -/
#guard_msgs in
#check 1...3 = 1...3

example : 1...3 = 1...<3 := rfl
example : 1 + 1...3 = 2...3 := rfl
example : 1 + 1...* = 2...* := rfl
example : *...1 + 2 = *...3 := rfl
example : 1 + 1<...=1 + 2 = 2<...=3 := rfl

/-- info: ∀ (i : Nat), i ∈ 0...3 → i < 3 : Prop -/
#guard_msgs in
#check ∀ i ∈ 0...3, i < 3

/-- info: 0 ∈ *...3 ∧ 1 ∈ 0...* : Prop -/
#guard_msgs in
#check 0 ∈ *...3 ∧ 1 ∈ 0...*

/-! Pipelines apply to the whole range. -/

/-- info: [1, 2] -/
#guard_msgs in
#eval 1...3 |> fun r => r.toList

/-- info: [1, 2] -/
#guard_msgs in
#eval (fun (r : Std.Rco Nat) => r.toList) <| 1...3

/-! Arithmetic in the bounds of `for` loops and slices. -/

def sumRange (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in n + 1...2 * n do
    s := s + i
  return s

/-- info: 9 -/
#guard_msgs in
#eval sumRange 3

def sumRangeTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in *...=2 * n do
    s := s + i
  return s

/-- info: 21 -/
#guard_msgs in
#eval sumRangeTo 3

/-- info: #[2, 3] -/
#guard_msgs in
#eval #[0, 1, 2, 3, 4][1 + 1...2 * 2].toArray

/-- info: #[2, 3, 4] -/
#guard_msgs in
#eval #[0, 1, 2, 3, 4][1 + 1...*].toArray

/-- info: #[0, 1, 2] -/
#guard_msgs in
#eval #[0, 1, 2, 3, 4][*...1 + 2].toArray

/-! The range notations are not associative. -/

open Lean in
def parseTerm (input : String) : CoreM Unit := do
  match Parser.runParserCategory (← getEnv) `term input with
  | .ok _ => IO.println "ok"
  | .error e => IO.println e

/-- info: <input>:1:5: expected end of input -/
#guard_msgs in
#eval parseTerm "1...2...3"

/-- info: <input>:1:6: expected end of input -/
#guard_msgs in
#eval parseTerm "1...=2<...=3"

/-- info: <input>:1:5: expected end of input -/
#guard_msgs in
#eval parseTerm "1...*...*"

/-- info: ok -/
#guard_msgs in
#eval parseTerm "(1...2)...3"
