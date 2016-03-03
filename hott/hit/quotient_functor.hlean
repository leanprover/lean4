/-
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz

Functoriality of quotients and a condition for when an equivalence is induced.
-/

import types.sigma .quotient
open eq is_equiv equiv prod prod.ops sigma sigma.ops

namespace quotient
section
  variables {A : Type} (R : A → A → Type)
             {B : Type} (Q : B → B → Type)
             (f : A → B) (k : Πa a' : A, R a a' → Q (f a) (f a'))
  include f k

  protected definition functor [reducible] : quotient R → quotient Q :=
  quotient.elim (λa, class_of Q (f a)) (λa a' r, eq_of_rel Q (k a a' r))

  variables [F : is_equiv f] [K : Πa a', is_equiv (k a a')]
  include F K

  protected definition functor_inv [reducible] : quotient Q → quotient R :=
  quotient.elim (λb, class_of R (f⁻¹ b))
                (λb b' q, eq_of_rel R ((k (f⁻¹ b) (f⁻¹ b'))⁻¹
                          ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q)))

  protected definition is_equiv [instance]
    : is_equiv (quotient.functor R Q f k):=
  begin
    fapply adjointify _ (quotient.functor_inv R Q f k),
    { intro qb, induction qb with b b b' q,
      { apply ap (class_of Q), apply right_inv },
      { apply eq_pathover, rewrite [ap_id,ap_compose' (quotient.elim _ _)],
        do 2 krewrite elim_eq_of_rel, rewrite (right_inv (k (f⁻¹ b) (f⁻¹ b'))),
        have H1 : pathover (λz : B × B, Q z.1 z.2)
          ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q)
          (prod_eq (right_inv f b) (right_inv f b')) q,
        begin apply pathover_of_eq_tr, krewrite [prod_eq_inv,prod_eq_transport] end,
        have H2 : square
          (ap (λx : (Σz : B × B, Q z.1 z.2), class_of Q x.1.1)
            (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1))
          (ap (λx : (Σz : B × B, Q z.1 z.2), class_of Q x.1.2)
            (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1))
          (eq_of_rel Q ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q))
          (eq_of_rel Q q),
        from
          natural_square (λw : (Σz : B × B, Q z.1 z.2), eq_of_rel Q w.2)
          (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1),
        krewrite (ap_compose' (class_of Q)) at H2,
        krewrite (ap_compose' (λz : B × B, z.1)) at H2,
        rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
        krewrite prod.ap_pr1 at H2, krewrite prod_eq_pr1 at H2,
        krewrite (ap_compose' (class_of Q) (λx : (Σz : B × B, Q z.1 z.2), x.1.2)) at H2,
        krewrite (ap_compose' (λz : B × B, z.2)) at H2,
        rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
        krewrite prod.ap_pr2 at H2, krewrite prod_eq_pr2 at H2,
        apply H2 } },
    { intro qa, induction qa with a a a' r,
      { apply ap (class_of R), apply left_inv },
      { apply eq_pathover, rewrite [ap_id,(ap_compose' (quotient.elim _ _))],
        do 2 krewrite elim_eq_of_rel,
        have H1 : pathover (λz : A × A, R z.1 z.2)
          ((left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r)
          (prod_eq (left_inv f a) (left_inv f a')) r,
        begin apply pathover_of_eq_tr, krewrite [prod_eq_inv,prod_eq_transport] end,
        have H2 : square
          (ap (λx : (Σz : A × A, R z.1 z.2), class_of R x.1.1)
            (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1))
          (ap (λx : (Σz : A × A, R z.1 z.2), class_of R x.1.2)
            (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1))
          (eq_of_rel R ((left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r))
          (eq_of_rel R r),
        begin
          exact
          natural_square (λw : (Σz : A × A, R z.1 z.2), eq_of_rel R w.2)
          (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1)
        end,
        krewrite (ap_compose' (class_of R)) at H2,
        krewrite (ap_compose' (λz : A × A, z.1)) at H2,
        rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
        krewrite prod.ap_pr1 at H2, krewrite prod_eq_pr1 at H2,
        krewrite (ap_compose' (class_of R) (λx : (Σz : A × A, R z.1 z.2), x.1.2)) at H2,
        krewrite (ap_compose' (λz : A × A, z.2)) at H2,
        rewrite sigma.ap_pr1 at H2, rewrite sigma_eq_pr1 at H2,
        krewrite prod.ap_pr2 at H2, krewrite prod_eq_pr2 at H2,
        have H3 :
          (k (f⁻¹ (f a)) (f⁻¹ (f a')))⁻¹
          ((right_inv f (f a))⁻¹ ▸ (right_inv f (f a'))⁻¹ ▸ k a a' r)
          = (left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r,
        begin
          rewrite [adj f a,adj f a',ap_inv',ap_inv'],
          rewrite [-(tr_compose _ f (left_inv f a')⁻¹ (k a a' r)),
                   -(tr_compose _ f (left_inv f a)⁻¹)],
          rewrite [-(fn_tr_eq_tr_fn (left_inv f a')⁻¹ (λx, k a x) r),
                   -(fn_tr_eq_tr_fn (left_inv f a)⁻¹
                     (λx, k x (f⁻¹ (f a')))),
                   left_inv (k _ _)]
        end,
        rewrite H3, apply H2 } }
  end
end

section
  variables {A : Type} (R : A → A → Type)
             {B : Type} (Q : B → B → Type)
             (f : A ≃ B) (k : Πa a' : A, R a a' ≃ Q (f a) (f a'))
  include f k

  /- This could also be proved using ua, but then it wouldn't compute -/
  protected definition equiv : quotient R ≃ quotient Q :=
  equiv.mk (quotient.functor R Q f k) _
end
end quotient
