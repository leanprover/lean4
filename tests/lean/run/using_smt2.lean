open smt_tactic

example (p q : Prop) : p → q → p :=
by using_smt $ return ()

example (p q : Prop) : ¬ p → q → ¬ p :=
by using_smt $ return ()

example (p q : Prop) : p → (p ↔ q) → q :=
by using_smt $ return ()

example (p q : Prop) : p → (p → q) → q :=
by using_smt $ return ()

example (p q : Prop) : (p → q) → p → q :=
by using_smt $ return ()

example (p q r : Prop) : (p → r → q) → r → p → q :=
by using_smt $ return ()

example (p q r s t o : Prop) : (p ∨ t → o ∨ r → q ∧ s) → r → p → q :=
by using_smt $ return ()

example (p q : Prop) (a b c : nat) : (p ∨ q → a = b ∨ a = c) → a ≠ b → p → c = a :=
by using_smt $ return ()

example (p q : Prop) [decidable p] [decidable q] (a b c : nat) : (if p ∨ q then (a = b ∨ a = c) else (a = 0)) → p → a ≠ b → c = a :=
by using_smt $ return ()

example (p q : Prop) : p → (p ↔ ¬q) → ¬q :=
by using_smt $ return ()

example (p q r s : Prop) : (p ∨ q → not (r ∨ s)) → p → not r :=
by using_smt $ return ()

example (p q r : Prop) (a b c : nat): (p → q ∧ r ∧ a = b + c) → p → (c + b = a ∧ r) :=
by using_smt $ return ()

example (a b c d : nat) : b = d → c = d → (if a > 10 then b else c) = b :=
by using_smt $ return ()
