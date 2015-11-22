set_option blast.init_depth 10
set_option blast.cc false

example (a b c : Prop) : b → c → b ∧ c :=
by blast

example (a b c : Prop) : b → c → c ∧ b :=
by blast

example (a b : Prop) : a → a ∨ b :=
by blast

example (a b : Prop) : b → a ∨ b :=
by blast

example (a b : Prop) : b → a ∨ a ∨ b :=
by blast

example (a b c : Prop) : b → c → a ∨ a ∨ (b ∧ c) :=
by blast

example (p q : nat → Prop) (a b : nat) : p a → q b → ∃ x, p x :=
by blast

example {A : Type} (p q : A → Prop) (a b : A) : q a → p b → ∃ x, p x :=
by blast

lemma foo₁ {A : Type} (p q : A → Prop) (a b : A) : q a → p b → ∃ x, (p x ∧ x = b) ∨ q x :=
by blast

lemma foo₂ {A : Type} (p q : A → Prop) (a b : A) : p b → ∃ x, q x ∨ (p x ∧ x = b) :=
by blast

reveal foo₁ foo₂
print foo₁
print foo₂
