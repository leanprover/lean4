-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import logic.classes.inhabited logic.connectives.eq

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

  theorem pair_eq {p1 p2 : prod A B} (H1 : pr1 p1 = pr1 p2) (H2 : pr2 p1 = pr2 p2) : p1 = p2 :=
  calc p1  = pair (pr1 p1) (pr2 p1) : symm (prod_ext p1)
       ... = pair (pr1 p2) (pr2 p1) : {H1}
       ... = pair (pr1 p2) (pr2 p2) : {H2}
       ... = p2                        : prod_ext p2

  theorem prod_inhabited (H1 : inhabited A) (H2 : inhabited B) : inhabited (prod A B) :=
  inhabited_elim H1 (λa, inhabited_elim H2 (λb, inhabited_intro (pair a b)))

end

instance prod_inhabited

end prod