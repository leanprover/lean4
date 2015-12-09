set_option blast.strategy "core_grind"

example (a b c : nat) : a = b ∨ a = c → b = c → b = a :=
by blast

example (f : nat → nat) (a b c : nat) : f a = f b ∨ f a = f c → f b = f c → f b = f a :=
by blast

definition ex1 (a : nat) : a = 0 → (λ x, x + a) = (λ x, x + 0) :=
by blast

print ex1

attribute Exists.intro [intro!] -- grind and core_grind only process [intro!] declarations

example (p q : nat → Prop) : (∃ x, p x ∧ q x) → (∃ x, q x) ∧ (∃ x, p x) :=
by blast

set_option blast.strategy "grind"

example (a b c : nat) : a = b ∨ a = c → b = c → b = a :=
by blast

example (f : nat → nat) (a b c : nat) : f a = f b ∨ f a = f c → f b = f c → f b = f a :=
by blast

example (a : nat) : a = 0 → (λ x, x + a) = (λ x, x + 0) :=
by blast

set_option trace.blast true
example (p q : nat → Prop) : (∃ x, p x ∧ q x) → (∃ x, q x) ∧ (∃ x, p x) :=
by blast
