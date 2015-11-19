open nat

example : ∀ (P Q : nat → Prop), (∀n, Q n → P n) → (∀n, Q n) → P 2 :=
by blast

example : ∀ (P Q : nat → Prop), (∀n m, Q m → P n) → Q 1 → P 2 :=
by blast

example : ∀ (P : nat → Prop) (F : Prop), (∀n, P n) → F → F ∧ P 2 :=
by blast

example : ∀ (F F' : Prop), F ∧ F' → F :=
by blast

attribute and.intro [backward]

example : ∀ (P Q R : nat → Prop) (F : Prop), (F ∧ (∀ n m, (Q m ∧ R n) → P n)) →
            (F → R 2) → Q 1 → P 2 ∧ F :=
by blast

-- We should get the following one with simplification and/or heuristic instantiation
-- example : ∀ (P Q : nat → Prop), (∀n, P n ∧ Q n) → P 2 :=
-- by blast

example : ∀ (P Q : nat → Prop) (F : Prop), (∀n, P n) ∧ (∀n, Q n) → P 2 :=
by blast

example : ∀ (F F' : Prop), F → F ∨ F' :=
by blast

example : ∀ (F F' : Prop), F ∨ F' → F' ∨ F :=
by blast

example : ∀ (F1 F2 F3 : Prop), ((¬F1 ∧ F3) ∨ (F2 ∧ ¬F3)) → (F2 → F1) → (F2 → F3) →  ¬F2 :=
by blast

example : ∀ (f : nat→Prop), f 2 → ∃x, f x :=
by blast

example : ∀ (f g : nat → Prop), (∀x, f x → g x) → (∃a, f a) → (∃a, g a) :=
by blast

-- We need heuristic inst for the following one
-- example : ∀ (P : nat → Prop), P 0 → (∀x, ¬ P x) → false :=
-- by blast

-- We need heuristic inst for the following one
-- example : ∀ (f g : nat → Prop), (∀x, f x = g x) → g 2 = f 2 :=
-- by blast

example : true ∧ true ∧ true ∧ true ∧ true ∧ true ∧ true :=
by blast

example : ∀ (P : nat → Prop), P 0 → (P 0 → P 1) → (P 1 → P 2) → (P 2) :=
by blast
