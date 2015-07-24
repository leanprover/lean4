/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Useful logical identities. Since we are not using propositional extensionality, some of the
calculations use the type class support provided by logic.instances.
-/
import logic.connectives logic.instances logic.quantifiers logic.cast
open relation decidable relation.iff_ops

theorem or.right_comm (a b c : Prop) : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b :=
calc
  (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) : or.assoc
    ... ↔ a ∨ (c ∨ b)       : {or.comm}
     ... ↔ (a ∨ c) ∨ b      : iff.symm or.assoc

theorem or.left_comm [simp] (a b c : Prop) : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
calc
  a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c : iff.symm or.assoc
    ... ↔ (b ∨ a) ∨ c       : {or.comm}
     ... ↔ b ∨ (a ∨ c)      : or.assoc

theorem and.right_comm (a b c : Prop) : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
calc
  (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) : and.assoc
    ... ↔ a ∧ (c ∧ b)       : {and.comm}
     ... ↔ (a ∧ c) ∧ b      : iff.symm and.assoc

theorem and.left_comm [simp] (a b c : Prop) : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) :=
calc
  a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c : iff.symm and.assoc
    ... ↔ (b ∧ a) ∧ c       : {and.comm}
     ... ↔ b ∧ (a ∧ c)      : and.assoc

theorem not_not_iff {a : Prop} [D : decidable a] : (¬¬a) ↔ a :=
iff.intro by_contradiction not_not_intro

theorem not_not_elim {a : Prop} [D : decidable a] : ¬¬a → a :=
by_contradiction

theorem not_or_iff_not_and_not {a b : Prop} : ¬(a ∨ b) ↔ ¬a ∧ ¬b :=
or.imp_distrib

theorem not_and_iff_not_or_not {a b : Prop} [Da : decidable a] :
  ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
iff.intro
  (λH, by_cases (λa, or.inr (not.mto (and.intro a) H)) or.inl)
  (or.rec (not.mto and.left) (not.mto and.right))

theorem imp_iff_not_or {a b : Prop} [Da : decidable a] : (a → b) ↔ ¬a ∨ b :=
iff.intro
  (by_cases (λHa H, or.inr (H Ha)) (λHa H, or.inl Ha))
  (or.rec not.elim imp.intro)

theorem not_implies_iff_and_not {a b : Prop} [Da : decidable a] :
  ¬(a → b) ↔ a ∧ ¬b :=
calc
  ¬(a → b) ↔ ¬(¬a ∨ b) : {imp_iff_not_or}
       ... ↔ ¬¬a ∧ ¬b  : not_or_iff_not_and_not
       ... ↔ a ∧ ¬b    : {not_not_iff}

theorem peirce {a b : Prop} [D : decidable a] : ((a → b) → a) → a :=
by_cases imp.intro (imp.syl imp.mp not.elim)

theorem forall_not_of_not_exists {A : Type} {p : A → Prop} [D : ∀x, decidable (p x)]
  (H : ¬∃x, p x) : ∀x, ¬p x :=
take x, by_cases
  (assume Hp : p x, absurd (exists.intro x Hp) H)
  imp.id

theorem forall_of_not_exists_not {A : Type} {p : A → Prop} [D : decidable_pred p] :
  ¬(∃ x, ¬p x) → ∀ x, p x :=
imp.syl (forall_imp_forall (λa, not_not_elim)) forall_not_of_not_exists

theorem exists_not_of_not_forall {A : Type} {p : A → Prop} [D : ∀x, decidable (p x)]
    [D' : decidable (∃x, ¬p x)] (H : ¬∀x, p x) :
  ∃x, ¬p x :=
by_contradiction (λH1, absurd (λx, not_not_elim (forall_not_of_not_exists H1 x)) H)

theorem exists_of_not_forall_not {A : Type} {p : A → Prop} [D : ∀x, decidable (p x)]
    [D' : decidable (∃x, p x)] (H : ¬∀x, ¬ p x) :
  ∃x, p x :=
by_contradiction (imp.syl H forall_not_of_not_exists)

theorem ne_self_iff_false {A : Type} (a : A) : (a ≠ a) ↔ false :=
iff.intro false.of_ne false.elim

theorem eq_self_iff_true [simp] {A : Type} (a : A) : (a = a) ↔ true :=
iff_true_intro rfl

theorem heq_self_iff_true [simp] {A : Type} (a : A) : (a == a) ↔ true :=
iff_true_intro (heq.refl a)

theorem iff_not_self [simp] (a : Prop) : (a ↔ ¬a) ↔ false :=
iff_false_intro (λH,
   have H' : ¬a, from (λHa, (mp H Ha) Ha),
   H' (iff.mpr H H'))

theorem true_iff_false [simp] : (true ↔ false) ↔ false :=
not_true ▸ (iff_not_self true)

theorem false_iff_true [simp] : (false ↔ true) ↔ false :=
not_false_iff ▸ (iff_not_self false)
