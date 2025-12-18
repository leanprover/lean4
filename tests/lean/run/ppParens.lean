/-!
# Tests for the `pp.parens` pretty printing option
-/

set_option pp.parens true

/-!
No parentheses around numeral.
-/
/-- info: 1 : Nat -/
#guard_msgs in #check 1

/-!
No parentheses around variable.
-/
/-- info: x : Nat -/
#guard_msgs in variable (x : Nat) in #check x

/-!
No parentheses around each individual function application.
-/
def f (x y z : Nat) : Nat := x + y + z
/-- info: f 1 2 3 : Nat -/
#guard_msgs in #check f 1 2 3

/-!
Example arithmetic expressions
-/
/-- info: (1 + (2 * 3)) + 4 : Nat -/
#guard_msgs in #check 1 + 2 * 3 + 4
/-- info: Nat.add_assoc : ∀ (n m k : Nat), (((n + m) + k) = (n + (m + k))) -/
#guard_msgs in #check (Nat.add_assoc)

/-!
Implication chains
-/
/-- info: p → (q → r) : Prop -/
#guard_msgs in variable (p q r : Prop) in #check p → q → r

/-!
No parentheses around list literals
-/
/-- info: [1, 2, 3] ++ [3, 4, 5] : List Nat -/
#guard_msgs in #check [1,2,3] ++ [3,4,5]

/-!
Parentheses around body of forall.
-/
/-- info: ∀ (p : (Nat → (Nat → Prop))), (p (1 + 2) 3) : Prop -/
#guard_msgs in #check ∀ (p : Nat → Nat → Prop), p (1 + 2) 3

/-!
Parentheses around branches of `if`.
-/
/-- info: if True then (1 + 2) else (2 + 3) : Nat -/
#guard_msgs in #check if True then 1 + 2 else 2 + 3
