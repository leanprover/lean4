-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad

import logic.classes.inhabited logic.connectives.eq

using inhabited

inductive prod (A B : Type) : Type :=
| pair : A → B → prod A B

precedence `×`:30
infixr × := prod

-- notation for n-ary tuples
notation `(` h `,` t:(foldl `,` (e r, pair r e) h) `)` := t

namespace prod

section

  parameters {A B : Type}

  abbreviation pr1 (p : prod A B) := prod_rec (λ x y, x) p
  abbreviation pr2 (p : prod A B) := prod_rec (λ x y, y) p

  theorem pr1_pair (a : A) (b : B) : pr1 (a, b) = a := refl a
  theorem pr2_pair (a : A) (b : B) : pr2 (a, b) = b := refl b

  -- TODO: remove prefix when we can protect it
  theorem pair_destruct {P : A × B → Prop} (p : A × B) (H : ∀a b, P (a, b)) : P p :=
  prod_rec H p

  theorem prod_ext (p : prod A B) : pair (pr1 p) (pr2 p) = p :=
  pair_destruct p (λx y, refl (x, y))

  theorem pair_eq {a1 a2 : A} {b1 b2 : B} (H1 : a1 = a2) (H2 : b1 = b2) : (a1, b1) = (a2, b2) :=
  subst H1 (subst H2 (refl _))

  theorem prod_eq {p1 p2 : prod A B} : ∀ (H1 : pr1 p1 = pr1 p2) (H2 : pr2 p1 = pr2 p2), p1 = p2 :=
  pair_destruct p1 (take a1 b1, pair_destruct p2 (take a2 b2 H1 H2, pair_eq H1 H2))

  theorem prod_inhabited (H1 : inhabited A) (H2 : inhabited B) : inhabited (prod A B) :=
  inhabited_destruct H1 (λa, inhabited_destruct H2 (λb, inhabited_mk (pair a b)))

end

instance prod_inhabited

end prod
