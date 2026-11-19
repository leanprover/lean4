/-!
# Tests for the expression tree elaborator (`binop%`, etc.)
-/

/-!
Some basic Int/Nat examples
-/

example (n : Nat) (i : Int) : n + i = i + n := by
  rw [Int.add_comm]

def f1 (a : Int) (b c : Nat) : Int :=
  a + (b - c)

def f2 (a : Int) (b c : Nat) : Int :=
  (b - c) + a

/--
info: def f1 : Int → Nat → Nat → Int :=
fun a b c => a + (↑b - ↑c)
-/
#guard_msgs in
#print f1

/--
info: def f2 : Int → Nat → Nat → Int :=
fun a b c => ↑b - ↑c + a
-/
#guard_msgs in
#print f2


/-!
Interaction with default instances for pow. This used to fail with not being able
to synthesize an `HMul Int Int Nat` instance because the type of
the result of `*` wasn't being set to `Int`.
-/

/-- info: ∀ (a : Nat) (b : Int), ↑a = id (↑a * b ^ 2) : Prop -/
#guard_msgs in
#check ∀ (a : Nat) (b : Int), a = id (a * b^2)
