
/-- Construct a natural number using `left`. -/
def zero : Nat := by
  left

example : zero = 0 := rfl

/-- Construct a natural number using `right`. -/
def two : Nat := by
  right
  exact 1

example : two = 2 := rfl

set_option linter.missingDocs false

/--
error: tactic 'left' failed,
left tactic works for inductive types with exactly 2 constructors
⊢ Unit
-/
#guard_msgs in
example : Unit := by
  left

inductive F
| a | b | c

/--
error: tactic 'left' failed,
left tactic works for inductive types with exactly 2 constructors
⊢ F
-/
#guard_msgs in
example : F := by
  left

def G := Nat

/-- Look through definitions. -/
example : G := by
  left

/--
error: tactic 'left' failed, target is not an inductive datatype
⊢ Type
-/
#guard_msgs in
example : Type := by
  left

example : Sum Nat (List Nat) := by
  left
  exact zero

example : Sum Nat (List Nat) := by
  right
  exact [0]

example : (1 = 1) ∨ (2 = 3) := by
  left
  rfl

example : (1 = 2) ∨ (3 = 3) := by
  right
  rfl
