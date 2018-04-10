universes u
variables {α : Sort u} {r p q : α → Prop} {P Q : ∀ x, p x → Prop} {a b c d : Prop}

@[simp] theorem exists_prop {p q : Prop} : (∃ h : p, q) ↔ p ∧ q := sorry
@[simp] theorem exists_and_distrib_right {q : Prop} {p : α → Prop} : (∃x, p x ∧ q) ↔ (∃x, p x) ∧ q := sorry
@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) := sorry
@[simp] theorem exists_imp_distrib : ((∃ x, p x) → b) ↔ ∀ x, p x → b := sorry

set_option trace.simplify.rewrite true
@[simp] theorem bex_imp_distrib : ((∃ x h, P x h) → b) ↔ (∀ x h, P x h → b) :=
by simp
