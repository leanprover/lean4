/-!
Test for definitional equalities of `Decidable` instances.
-/

variable {p q : Prop} {a b c : Bool} [Decidable p] [Decidable q]

/-!
Definitional equalities for basic propositional connectives
-/

example : decide (p ∧ q) = (decide p && decide q) := rfl
example : decide (p ∨ q) = (decide p || decide q) := rfl
example : decide (¬ p) = !decide p := rfl
example : decide (p ↔ q) = (decide p == decide q) := rfl
example : decide (p = q) = (decide p == decide q) := rfl

/-!
Definitional equalities for boolean equality
-/

example : decide (a = b) = (a == b) := rfl
example : decide (a = true) = a := rfl
example : decide (a = false) = !a := rfl
example : decide (a ∧ b) = (a && b) := rfl
example : decide (a ∨ b) = (a || b) := rfl
example : decide (¬a) = !a := rfl
