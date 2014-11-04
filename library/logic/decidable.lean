-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import logic.connectives data.empty

inductive decidable [class] (p : Prop) : Type :=
inl : p  → decidable p,
inr : ¬p → decidable p

namespace decidable
  definition true_decidable [instance] : decidable true :=
  inl trivial

  definition false_decidable [instance] : decidable false :=
  inr not_false_trivial

  variables {p q : Prop}

  definition rec_on_true [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : p) (H4 : H1 H3)
      : rec_on H H1 H2 :=
  rec_on H (λh, H4) (λh, false.rec _ (h H3))

  definition rec_on_false [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : ¬p) (H4 : H2 H3)
      : rec_on H H1 H2 :=
  rec_on H (λh, false.rec _ (H3 h)) (λh, H4)

  theorem irrelevant [instance] : subsingleton (decidable p) :=
  subsingleton.intro (fun d1 d2,
    decidable.rec
      (assume Hp1 : p, decidable.rec
        (assume Hp2  : p,  congr_arg inl (eq.refl Hp1)) -- using proof irrelevance for Prop
        (assume Hnp2 : ¬p, absurd Hp1 Hnp2)
        d2)
      (assume Hnp1 : ¬p, decidable.rec
        (assume Hp2  : p,  absurd Hp2 Hnp1)
        (assume Hnp2 : ¬p, congr_arg inr (eq.refl Hnp1)) -- using proof irrelevance for Prop
        d2)
      d1)

  definition by_cases {q : Type} [C : decidable p] (Hpq : p → q) (Hnpq : ¬p → q) : q :=
  rec_on C (assume Hp, Hpq Hp) (assume Hnp, Hnpq Hnp)

  theorem em (p : Prop) [H : decidable p] : p ∨ ¬p :=
  by_cases (λ Hp, or.inl Hp) (λ Hnp, or.inr Hnp)

  theorem by_contradiction [Hp : decidable p] (H : ¬p → false) : p :=
  by_cases
    (assume H1 : p, H1)
    (assume H1 : ¬p, false_elim (H H1))

  definition and_decidable [instance] (Hp : decidable p) (Hq : decidable q) : decidable (p ∧ q) :=
  rec_on Hp
    (assume Hp  : p, rec_on Hq
      (assume Hq  : q,  inl (and.intro Hp Hq))
      (assume Hnq : ¬q, inr (and.not_right p Hnq)))
    (assume Hnp : ¬p, inr (and.not_left q Hnp))

  definition or_decidable [instance] (Hp : decidable p) (Hq : decidable q) : decidable (p ∨ q) :=
  rec_on Hp
    (assume Hp  : p, inl (or.inl Hp))
    (assume Hnp : ¬p, rec_on Hq
      (assume Hq  : q,  inl (or.inr Hq))
      (assume Hnq : ¬q, inr (or.not_intro Hnp Hnq)))

  definition not_decidable [instance] (Hp : decidable p) : decidable (¬p) :=
  rec_on Hp
    (assume Hp,  inr (not_not_intro Hp))
    (assume Hnp, inl Hnp)

  definition implies_decidable [instance] (Hp : decidable p) (Hq : decidable q) : decidable (p → q) :=
  rec_on Hp
    (assume Hp  : p, rec_on Hq
      (assume Hq  : q,  inl (assume H, Hq))
      (assume Hnq : ¬q, inr (assume H : p → q, absurd (H Hp) Hnq)))
    (assume Hnp : ¬p, inl (assume Hp, absurd Hp Hnp))

  definition iff_decidable [instance] (Hp : decidable p) (Hq : decidable q) : decidable (p ↔ q) := _

  definition decidable_iff_equiv (Hp : decidable p) (H : p ↔ q) : decidable q :=
  rec_on Hp
    (assume Hp : p,   inl (iff.elim_left H Hp))
    (assume Hnp : ¬p, inr (iff.elim_left (iff.flip_sign H) Hnp))

  definition decidable_eq_equiv (Hp : decidable p) (H : p = q) : decidable q :=
  decidable_iff_equiv Hp (eq_to_iff H)

  protected theorem rec_subsingleton [instance] [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type}
      (H3 : Π(h : p), subsingleton (H1 h)) (H4 : Π(h : ¬p), subsingleton (H2 h))
      : subsingleton (rec_on H H1 H2) :=
  rec_on H (λh, H3 h) (λh, H4 h) --this can be proven using dependent version of "by_cases"
end decidable

definition decidable_rel  {A : Type} (R : A   →   Prop) := Π (a   : A), decidable (R a)
definition decidable_rel2 {A : Type} (R : A → A → Prop) := Π (a b : A), decidable (R a b)
definition decidable_eq (A : Type) := decidable_rel2 (@eq A)

--empty cannot depend on decidable, so we prove this here
protected definition empty.has_decidable_eq [instance] : decidable_eq empty :=
take (a b : empty), decidable.inl (!empty.elim a)
