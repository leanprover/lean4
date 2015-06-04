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

theorem or.left_comm (a b c : Prop) : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
calc
  a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c : iff.symm or.assoc
    ... ↔ (b ∨ a) ∨ c       : {or.comm}
     ... ↔ b ∨ (a ∨ c)      : or.assoc

theorem and.right_comm (a b c : Prop) : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
calc
  (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) : and.assoc
    ... ↔ a ∧ (c ∧ b)       : {and.comm}
     ... ↔ (a ∧ c) ∧ b      : iff.symm and.assoc

theorem and.left_comm (a b c : Prop) : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) :=
calc
  a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c : iff.symm and.assoc
    ... ↔ (b ∧ a) ∧ c       : {and.comm}
     ... ↔ b ∧ (a ∧ c)      : and.assoc

theorem not_not_iff {a : Prop} [D : decidable a] : (¬¬a) ↔ a :=
iff.intro
  (assume H : ¬¬a,
    by_cases (assume H' : a, H') (assume H' : ¬a, absurd H' H))
  (assume H : a, assume H', H' H)

theorem not_not_elim {a : Prop} [D : decidable a] (H : ¬¬a) : a :=
iff.mp not_not_iff H

theorem not_true_iff_false : ¬true ↔ false :=
iff.intro (assume H, H trivial) false.elim

theorem not_false_iff_true : ¬false ↔ true :=
iff.intro (assume H, trivial) (assume H H', H')

theorem not_or_iff_not_and_not {a b : Prop} [Da : decidable a] [Db : decidable b] :
  ¬(a ∨ b) ↔ ¬a ∧ ¬b :=
iff.intro
  (assume H, or.elim (em a)
    (assume Ha, absurd (or.inl Ha) H)
    (assume Hna, or.elim (em b)
      (assume Hb, absurd (or.inr Hb) H)
      (assume Hnb, and.intro Hna Hnb)))
  (assume (H : ¬a ∧ ¬b) (N : a ∨ b),
    or.elim N
      (assume Ha, absurd Ha (and.elim_left H))
      (assume Hb, absurd Hb (and.elim_right H)))

theorem not_and_iff_not_or_not {a b : Prop} [Da : decidable a] [Db : decidable b] :
  ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
iff.intro
  (assume H, or.elim (em a)
    (assume Ha, or.elim (em b)
      (assume Hb, absurd (and.intro Ha Hb) H)
      (assume Hnb, or.inr Hnb))
    (assume Hna, or.inl Hna))
  (assume (H : ¬a ∨ ¬b) (N : a ∧ b),
    or.elim H
      (assume Hna, absurd (and.elim_left N) Hna)
      (assume Hnb, absurd (and.elim_right N) Hnb))

theorem imp_iff_not_or {a b : Prop} [Da : decidable a] : (a → b) ↔ ¬a ∨ b :=
iff.intro
  (assume H : a → b, (or.elim (em a)
    (assume Ha  : a,   or.inr (H Ha))
    (assume Hna : ¬a, or.inl Hna)))
  (assume (H : ¬a ∨ b) (Ha : a),
    or_resolve_right H (not_not_iff⁻¹ ▸ Ha))

theorem not_implies_iff_and_not {a b : Prop} [Da : decidable a] [Db : decidable b] :
  ¬(a → b) ↔ a ∧ ¬b :=
calc
  ¬(a → b) ↔ ¬(¬a ∨ b) : {imp_iff_not_or}
       ... ↔ ¬¬a ∧ ¬b  : not_or_iff_not_and_not
       ... ↔ a ∧ ¬b    : {not_not_iff}

theorem peirce {a b : Prop} [D : decidable a] : ((a → b) → a) → a :=
assume H, by_contradiction (assume Hna : ¬a,
  have Hnna : ¬¬a, from not_not_of_not_implies (mt H Hna),
  absurd (not_not_elim Hnna) Hna)

theorem forall_not_of_not_exists {A : Type} {p : A → Prop} [D : ∀x, decidable (p x)]
  (H : ¬∃x, p x) : ∀x, ¬p x :=
take x, or.elim (em (p x))
  (assume Hp : p x,   absurd (exists.intro x Hp) H)
  (assume Hnp : ¬p x, Hnp)

theorem forall_of_not_exists_not {A : Type} {p : A → Prop} [D : decidable_pred p] :
  ¬(∃ x, ¬p x) → ∀ x, p x :=
assume Hne, take x, by_contradiction (assume Hnp : ¬ p x, Hne (exists.intro x Hnp))

theorem exists_not_of_not_forall {A : Type} {p : A → Prop} [D : ∀x, decidable (p x)]
    [D' : decidable (∃x, ¬p x)] (H : ¬∀x, p x) :
  ∃x, ¬p x :=
by_contradiction
  (assume H1 : ¬∃x, ¬p x,
    have H2 : ∀x, ¬¬p x, from forall_not_of_not_exists H1,
    have H3 : ∀x, p x, from take x, not_not_elim (H2 x),
    absurd H3 H)

theorem exists_of_not_forall_not {A : Type} {p : A → Prop} [D : ∀x, decidable (p x)]
    [D' : decidable (∃x, ¬¬p x)] (H : ¬∀x, ¬ p x) :
  ∃x, p x :=
obtain x (H : ¬¬ p x), from exists_not_of_not_forall H,
exists.intro x (not_not_elim H)

theorem ne_self_iff_false {A : Type} (a : A) : (a ≠ a) ↔ false :=
iff.intro
  (assume H, false.of_ne H)
  (assume H, false.elim H)

theorem eq_self_iff_true {A : Type} (a : A) : (a = a) ↔ true :=
iff_true_intro rfl

theorem heq_self_iff_true {A : Type} (a : A) : (a == a) ↔ true :=
iff_true_intro (heq.refl a)

theorem iff_not_self (a : Prop) : (a ↔ ¬a) ↔ false :=
iff.intro
  (assume H,
    have H' : ¬a, from assume Ha, (H ▸ Ha) Ha,
    H' (H⁻¹ ▸ H'))
  (assume H, false.elim H)

theorem true_iff_false : (true ↔ false) ↔ false :=
not_true_iff_false ▸ (iff_not_self true)

theorem false_iff_true : (false ↔ true) ↔ false :=
not_false_iff_true ▸ (iff_not_self false)

theorem iff_true_iff (a : Prop) : (a ↔ true) ↔ a :=
iff.intro (assume H, of_iff_true H) (assume H, iff_true_intro H)

theorem iff_false_iff_not (a : Prop) : (a ↔ false) ↔ ¬a :=
iff.intro (assume H, not_of_iff_false H) (assume H, iff_false_intro H)
