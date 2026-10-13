module

/-!
Tests for the `recall` and `recall?` commands.
-/

recall Nat.add_comm (n m : Nat) : n + m = m + n

recall Nat.add_comm {n m : Nat} : n + m = m + n

/-- The additive commutativity of natural numbers. -/
recall Nat.add_comm (n m : Nat) : n + m = m + n

def answer := 42

recall answer : Nat := 42
recall answer : Nat

/--
error: value mismatch
  answer
has value
  43
but is expected to have value
  42
-/
#guard_msgs in
recall answer : Nat := 43

/--
info: Try this:
  [apply] recall Nat.add_comm (n m : Nat) : n + m = m + n
---
error: Type mismatch
  Nat.add_comm
has type
  ∀ (n m : Nat), n + m = m + m
but is expected to have type
  ∀ (n m : Nat), n + m = m + n
-/
#guard_msgs in
recall Nat.add_comm (n m : Nat) : n + m = m + m

namespace Example

def value := 7

recall value : Nat

end Example

open Example in
recall value : Nat

/--
info: Try this:
  [apply] recall Nat.add_comm (n m : Nat) : n + m = m + n
-/
#guard_msgs in recall? Nat.add_comm

/-- error: Unknown constant `nonexistent` -/
#guard_msgs in
recall? nonexistent
