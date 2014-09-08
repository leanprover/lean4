-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad
import logic.classes.inhabited logic.core.eq logic.classes.decidable

-- data.prod
-- =========

open inhabited decidable

-- The cartesian product.
inductive prod (A B : Type) : Type :=
  mk : A → B → prod A B

abbreviation pair := @prod.mk
infixr `×` := prod

-- notation for n-ary tuples
notation `(` h `,` t:(foldl `,` (e r, prod.mk r e) h) `)` := t

namespace prod
section
  parameters {A B : Type}

  abbreviation pr1 (p : prod A B) := rec (λ x y, x) p
  abbreviation pr2 (p : prod A B) := rec (λ x y, y) p

  theorem pr1_pair (a : A) (b : B) : pr1 (a, b) = a :=
  rfl

  theorem pr2_pair (a : A) (b : B) : pr2 (a, b) = b :=
  rfl

  theorem destruct [protected] {P : A × B → Prop} (p : A × B) (H : ∀a b, P (a, b)) : P p :=
  rec H p

  theorem prod_ext (p : prod A B) : pair (pr1 p) (pr2 p) = p :=
  destruct p (λx y, eq.refl (x, y))

  open eq_ops

  theorem pair_eq {a1 a2 : A} {b1 b2 : B} (H1 : a1 = a2) (H2 : b1 = b2) : (a1, b1) = (a2, b2) :=
  H1 ▸ H2 ▸ rfl

  theorem equal [protected] {p1 p2 : prod A B} : ∀ (H1 : pr1 p1 = pr1 p2) (H2 : pr2 p1 = pr2 p2), p1 = p2 :=
  destruct p1 (take a1 b1, destruct p2 (take a2 b2 H1 H2, pair_eq H1 H2))

  theorem is_inhabited [protected] [instance] (H1 : inhabited A) (H2 : inhabited B) : inhabited (prod A B) :=
  inhabited.destruct H1 (λa, inhabited.destruct H2 (λb, inhabited.mk (pair a b)))

  theorem has_decidable_eq [protected] [instance] (H1 : decidable_eq A) (H2 : decidable_eq B) : decidable_eq (A × B) :=
  decidable_eq.intro (λ (u v : A × B),
    have H3 : u = v ↔ (pr1 u = pr1 v) ∧ (pr2 u = pr2 v), from
      iff.intro
        (assume H, H ▸ and.intro rfl rfl)
        (assume H, and.elim H (assume H4 H5, equal H4 H5)),
    decidable_iff_equiv _ (iff.symm H3))
end
end prod
