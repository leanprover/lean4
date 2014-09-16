-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jeremy Avigad, Leonardo de Moura

-- logic.connectives.identities
-- ============================

-- Useful logical identities. In the absence of propositional extensionality, some of the
-- calculations use the type class support provided by logic.connectives.instances

import logic.core.instances logic.core.decidable logic.core.quantifiers logic.core.cast

open relation decidable relation.iff_ops

theorem or_right_comm (a b c : Prop) : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b :=
calc
  (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) : or.assoc
    ... ↔ a ∨ (c ∨ b)       : {or.comm}
     ... ↔ (a ∨ c) ∨ b      : iff.symm or.assoc

theorem or_left_comm (a b c : Prop) : a ∨ (b ∨ c)↔ b ∨ (a ∨ c) :=
calc
  a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c : iff.symm or.assoc
    ... ↔ (b ∨ a) ∨ c       : {or.comm}
     ... ↔ b ∨ (a ∨ c)      : or.assoc

theorem and_right_comm (a b c : Prop) : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
calc
  (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) : and.assoc
    ... ↔ a ∧ (c ∧ b)       : {and.comm}
     ... ↔ (a ∧ c) ∧ b      : iff.symm and.assoc

theorem and_left_comm (a b c : Prop) : a ∧ (b ∧ c)↔ b ∧ (a ∧ c) :=
calc
  a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c : iff.symm and.assoc
    ... ↔ (b ∧ a) ∧ c       : {and.comm}
     ... ↔ b ∧ (a ∧ c)      : and.assoc


theorem not_not_iff {a : Prop} {D : decidable a} : (¬¬a) ↔ a :=
iff.intro
  (assume H : ¬¬a,
    by_cases (assume H' : a, H') (assume H' : ¬a, absurd H' H))
  (assume H : a, assume H', H' H)

theorem not_not_elim {a : Prop} {D : decidable a} (H : ¬¬a) : a :=
iff.mp not_not_iff H

theorem not_true : (¬true) ↔ false :=
iff.intro (assume H, H trivial) false_elim

theorem not_false : (¬false) ↔ true :=
iff.intro (assume H, trivial) (assume H H', H')

theorem not_or {a b : Prop} {Da : decidable a} {Db : decidable b} : (¬(a ∨ b)) ↔ (¬a ∧ ¬b) :=
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

theorem not_and {a b : Prop} {Da : decidable a} {Db : decidable b} : (¬(a ∧ b)) ↔ (¬a ∨ ¬b) :=
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

theorem imp_or {a b : Prop} {Da : decidable a} : (a → b) ↔ (¬a ∨ b) :=
iff.intro
  (assume H : a → b, (or.elim (em a)
    (assume Ha  : a,   or.inr (H Ha))
    (assume Hna : ¬a, or.inl Hna)))
  (assume (H : ¬a ∨ b) (Ha : a),
    or.resolve_right H (not_not_iff⁻¹ ▸ Ha))

theorem not_implies {a b : Prop} {Da : decidable a} {Db : decidable b} : (¬(a → b)) ↔ (a ∧ ¬b) :=
calc (¬(a → b)) ↔ (¬(¬a ∨ b)) : {imp_or}
            ... ↔ (¬¬a ∧ ¬b)  : not_or
            ... ↔ (a ∧ ¬b)    : {not_not_iff}

theorem peirce {a b : Prop} {D : decidable a} : ((a → b) → a) → a :=
assume H, by_contradiction (assume Hna : ¬a,
  have Hnna : ¬¬a, from not_implies_left (mt H Hna),
  absurd (not_not_elim Hnna) Hna)

theorem not_exists_forall {A : Type} {P : A → Prop} {D : ∀x, decidable (P x)}
    (H : ¬∃x, P x) : ∀x, ¬P x :=
take x, or.elim (em (P x))
  (assume Hp : P x,   absurd (exists_intro x Hp) H)
  (assume Hn : ¬P x, Hn)

theorem not_forall_exists {A : Type} {P : A → Prop} {D : ∀x, decidable (P x)}
    {D' : decidable (∃x, ¬P x)} (H : ¬∀x, P x) :
  ∃x, ¬P x :=
@by_contradiction _ D' (assume H1 : ¬∃x, ¬P x,
  have H2 : ∀x, ¬¬P x, from @not_exists_forall _ _ (take x, not_decidable (D x)) H1,
  have H3 : ∀x, P x, from take x, @not_not_elim _ (D x) (H2 x),
  absurd H3 H)

theorem iff_true_intro {a : Prop} (H : a) : a ↔ true :=
iff.intro
  (assume H1 : a,    trivial)
  (assume H2 : true, H)

theorem iff_false_intro {a : Prop} (H : ¬a) : a ↔ false :=
iff.intro
  (assume H1 : a,     absurd H1 H)
  (assume H2 : false, false_elim H2)

theorem a_neq_a {A : Type} (a : A) : (a ≠ a) ↔ false :=
iff.intro
  (assume H, a_neq_a_elim H)
  (assume H, false_elim H)

theorem eq_id {A : Type} (a : A) : (a = a) ↔ true :=
iff_true_intro rfl

theorem heq_id {A : Type} (a : A) : (a == a) ↔ true :=
iff_true_intro (hrefl a)

theorem a_iff_not_a (a : Prop) : (a ↔ ¬a) ↔ false :=
iff.intro
  (assume H,
    have H' : ¬a, from assume Ha, (H ▸ Ha) Ha,
    H' (H⁻¹ ▸ H'))
  (assume H, false_elim H)

theorem true_eq_false : (true ↔ false) ↔ false :=
not_true ▸ (a_iff_not_a true)

theorem false_eq_true : (false ↔ true) ↔ false :=
not_false ▸ (a_iff_not_a false)

theorem a_eq_true (a : Prop) : (a ↔ true) ↔ a :=
iff.intro (assume H, iff.true_elim H) (assume H, iff_true_intro H)

theorem a_eq_false (a : Prop) : (a ↔ false) ↔ ¬a :=
iff.intro (assume H, iff.false_elim H) (assume H, iff_false_intro H)
