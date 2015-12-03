constants P Q : nat → Prop
inductive foo : nat → Prop :=
| intro1 : ∀ n, P n → foo n
| intro2 : ∀ n, P n → foo n

definition bar (n : nat) : foo n → P n :=
by blast

print bar
/-
definition bar : ∀ (n : ℕ), foo n → P n :=
foo.rec (λ (n : ℕ) (H.3 : P n), H.3) (λ (n : ℕ) (H.3 : P n), H.3)
-/

definition baz (n : nat) : foo n → foo n ∧ P n :=
by blast --loops
