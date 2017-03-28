/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.propext init.classical

/- Lemmas use by the congruence closure module -/

lemma iff_eq_of_eq_true_left {a b : Prop} (h : a = true) : (a ↔ b) = b :=
h.symm ▸ propext (true_iff _)

lemma iff_eq_of_eq_true_right {a b : Prop} (h : b = true) : (a ↔ b) = a :=
h.symm ▸ propext (iff_true _)
lemma iff_eq_true_of_eq {a b : Prop} (h : a = b) : (a ↔ b) = true :=
h ▸ propext (iff_self _)

lemma and_eq_of_eq_true_left {a b : Prop} (h : a = true) : (a ∧ b) = b :=
h.symm ▸ propext (true_and  _)

lemma and_eq_of_eq_true_right {a b : Prop} (h : b = true) : (a ∧ b) = a :=
h.symm ▸ propext (and_true _)

lemma and_eq_of_eq_false_left {a b : Prop} (h : a = false) : (a ∧ b) = false :=
h.symm ▸ propext (false_and _)

lemma and_eq_of_eq_false_right {a b : Prop} (h : b = false) : (a ∧ b) = false :=
h.symm ▸ propext (and_false _)

lemma and_eq_of_eq {a b : Prop} (h : a = b) : (a ∧ b) = a :=
h ▸ propext (and_self _)

lemma or_eq_of_eq_true_left {a b : Prop} (h : a = true) : (a ∨ b) = true :=
h.symm ▸ propext (true_or  _)

lemma or_eq_of_eq_true_right {a b : Prop} (h : b = true) : (a ∨ b) = true :=
h.symm ▸ propext (or_true _)

lemma or_eq_of_eq_false_left {a b : Prop} (h : a = false) : (a ∨ b) = b :=
h.symm ▸ propext (false_or _)

lemma or_eq_of_eq_false_right {a b : Prop} (h : b = false) : (a ∨ b) = a :=
h.symm ▸ propext (or_false _)

lemma or_eq_of_eq {a b : Prop} (h : a = b) : (a ∨ b) = a :=
h ▸ propext (or_self _)

lemma imp_eq_of_eq_true_left {a b : Prop} (h : a = true) : (a → b) = b :=
h.symm ▸ propext (iff.intro (λ h, h trivial) (λ h₁ h₂, h₁))

lemma imp_eq_of_eq_true_right {a b : Prop} (h : b = true) : (a → b) = true :=
h.symm ▸ propext (iff.intro (λ h, trivial) (λ h₁ h₂, h₁))

lemma imp_eq_of_eq_false_left {a b : Prop} (h : a = false) : (a → b) = true :=
h.symm ▸ propext (iff.intro (λ h, trivial) (λ h₁ h₂, false.elim h₂))

lemma imp_eq_of_eq_false_right {a b : Prop} (h : b = false) : (a → b) = not a :=
h.symm ▸ propext (iff.intro (λ h, h) (λ hna ha, hna ha))

/- Remark: the congruence closure module will only use the following lemma is
   cc_config.em is tt. -/
lemma not_imp_eq_of_eq_false_right {a b : Prop} (h : b = false) : (not a → b) = a :=
h.symm ▸ propext (iff.intro (λ h', classical.by_contradiction (λ hna, h' hna)) (λ ha hna, hna ha))

lemma imp_eq_true_of_eq {a b : Prop} (h : a = b) : (a → b) = true :=
h ▸ propext (iff.intro (λ h, trivial) (λ h ha, ha))

lemma not_eq_of_eq_true {a : Prop} (h : a = true) : (not a) = false :=
h.symm ▸ propext not_true_iff

lemma not_eq_of_eq_false {a : Prop} (h : a = false) : (not a) = true :=
h.symm ▸ propext not_false_iff

lemma false_of_a_eq_not_a {a : Prop} (h : a = not a) : false :=
have not a, from λ ha, absurd ha (eq.mp h ha),
absurd (eq.mpr h this) this

universes u

lemma if_eq_of_eq_true {c : Prop} [d : decidable c] {α : Sort u} (t e : α) (h : c = true) : (@ite c d α t e) = t :=
if_pos (of_eq_true h)

lemma if_eq_of_eq_false {c : Prop} [d : decidable c] {α : Sort u} (t e : α) (h : c = false) : (@ite c d α t e) = e :=
if_neg (not_of_eq_false h)

lemma if_eq_of_eq (c : Prop) [d : decidable c] {α : Sort u} {t e : α} (h : t = e) : (@ite c d α t e) = t :=
match d with
| (is_true hc)   := rfl
| (is_false hnc) := eq.symm h
end

lemma eq_true_of_and_eq_true_left {a b : Prop} (h : (a ∧ b) = true) : a = true :=
eq_true_intro (and.left (of_eq_true h))

lemma eq_true_of_and_eq_true_right {a b : Prop} (h : (a ∧ b) = true) : b = true :=
eq_true_intro (and.right (of_eq_true h))

lemma eq_false_of_or_eq_false_left {a b : Prop} (h : (a ∨ b) = false) : a = false :=
eq_false_intro (λ ha, false.elim (eq.mp h (or.inl ha)))

lemma eq_false_of_or_eq_false_right {a b : Prop} (h : (a ∨ b) = false) : b = false :=
eq_false_intro (λ hb, false.elim (eq.mp h (or.inr hb)))

lemma eq_false_of_not_eq_true {a : Prop} (h : (not a) = true) : a = false :=
eq_false_intro (λ ha, absurd ha (eq.mpr h trivial))

/- Remark: the congruence closure module will only use the following lemma is
   cc_config.em is tt. -/
lemma eq_true_of_not_eq_false {a : Prop} (h : (not a) = false) : a = true :=
eq_true_intro (classical.by_contradiction (λ hna, eq.mp h hna))

lemma ne_of_eq_of_ne {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c :=
h₁.symm ▸ h₂

lemma ne_of_ne_of_eq {α : Sort u} {a b c : α} (h₁ : a ≠ b) (h₂ : b = c) : a ≠ c :=
h₂ ▸ h₁
