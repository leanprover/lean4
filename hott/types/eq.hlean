/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.eq
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about path types (identity types)
-/

open eq sigma sigma.ops equiv is_equiv

namespace eq
  /- Path spaces -/

  variables {A B : Type} {a a1 a2 a3 a4 : A} {b b1 b2 : B} {f g : A → B} {h : B → A}

  /- The path spaces of a path space are not, of course, determined; they are just the
      higher-dimensional structure of the original space. -/

  /- some lemmas about whiskering -/

  definition whisker_left_con_right (p : a1 = a2) {q q' q'' : a2 = a3} (r : q = q') (s : q' = q'')
    : whisker_left p (r ⬝ s) = whisker_left p r ⬝ whisker_left p s :=
  begin
    cases p, cases r, cases s, apply idp
  end

  definition whisker_right_con_right {p p' p'' : a1 = a2} (q : a2 = a3) (r : p = p') (s : p' = p'')
    : whisker_right (r ⬝ s) q = whisker_right r q ⬝ whisker_right s q :=
  begin
    cases q, cases r, cases s, apply idp
  end

  definition whisker_left_con_left (p : a1 = a2) (p' : a2 = a3) {q q' : a3 = a4} (r : q = q')
    : whisker_left (p ⬝ p') r = !con.assoc ⬝ whisker_left p (whisker_left p' r) ⬝ !con.assoc' :=
  begin
    cases p', cases p, cases r, cases q, apply idp
  end

  definition whisker_right_con_left {p p' : a1 = a2} (q : a2 = a3) (q' : a3 = a4) (r : p = p')
    : whisker_right r (q ⬝ q') = !con.assoc' ⬝ whisker_right (whisker_right r q) q' ⬝ !con.assoc :=
  begin
    cases q', cases q, cases r, cases p, apply idp
  end

  definition whisker_left_inv_left (p : a2 = a1) {q q' : a2 = a3} (r : q = q')
    : !con_inv_cancel_left⁻¹ ⬝ whisker_left p (whisker_left p⁻¹ r) ⬝ !con_inv_cancel_left = r :=
  begin
    cases p, cases r, cases q, apply idp
  end

  /- Transporting in path spaces.

     There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

     - `l` means the left endpoint varies
     - `r` means the right endpoint varies
     - `F` means application of a function to that (varying) endpoint.
  -/

  definition transport_eq_l (p : a1 = a2) (q : a1 = a3)
    : transport (λx, x = a3) p q = p⁻¹ ⬝ q :=
  by cases p; cases q; apply idp

  definition transport_eq_r (p : a2 = a3) (q : a1 = a2)
    : transport (λx, a1 = x) p q = q ⬝ p :=
  by cases p; cases q; apply idp

  definition transport_eq_lr (p : a1 = a2) (q : a1 = a1)
    : transport (λx, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  begin
  apply (eq.rec_on p),
  apply inverse, apply concat,
    apply con_idp,
  apply idp_con
  end

  definition transport_eq_Fl (p : a1 = a2) (q : f a1 = b)
    : transport (λx, f x = b) p q = (ap f p)⁻¹ ⬝ q :=
  by cases p; cases q; apply idp

  definition transport_eq_Fr (p : a1 = a2) (q : b = f a1)
    : transport (λx, b = f x) p q = q ⬝ (ap f p) :=
  by cases p; apply idp

  definition transport_eq_FlFr (p : a1 = a2) (q : f a1 = g a1)
    : transport (λx, f x = g x) p q = (ap f p)⁻¹ ⬝ q ⬝ (ap g p) :=
  begin
  apply (eq.rec_on p),
  apply inverse, apply concat,
    apply con_idp,
  apply idp_con
  end

  definition transport_eq_FlFr_D {B : A → Type} {f g : Πa, B a}
    (p : a1 = a2) (q : f a1 = g a1)
      : transport (λx, f x = g x) p q = (apd f p)⁻¹ ⬝ ap (transport B p) q ⬝ (apd g p) :=
  begin
  apply (eq.rec_on p),
  apply inverse,
  apply concat, apply con_idp,
  apply concat, apply idp_con,
  apply ap_id
  end

  definition transport_eq_FFlr (p : a1 = a2) (q : h (f a1) = a1)
    : transport (λx, h (f x) = x) p q = (ap h (ap f p))⁻¹ ⬝ q ⬝ p :=
  begin
  apply (eq.rec_on p),
  apply inverse,
  apply concat, apply con_idp,
  apply idp_con,
  end

  definition transport_eq_lFFr (p : a1 = a2) (q : a1 = h (f a1))
    : transport (λx, x = h (f x)) p q = p⁻¹ ⬝ q ⬝ (ap h (ap f p)) :=
  begin
  apply (eq.rec_on p),
  apply inverse,
  apply concat, apply con_idp,
  apply idp_con,
  end


  -- The Functorial action of paths is [ap].

  /- Equivalences between path spaces -/

  /- [ap_closed] is in init.equiv  -/

  definition equiv_ap (f : A → B) [H : is_equiv f] (a1 a2 : A)
    : (a1 = a2) ≃ (f a1 = f a2) :=
  equiv.mk _ _

  /- Path operations are equivalences -/

  definition is_equiv_eq_inverse (a1 a2 : A) : is_equiv (@inverse A a1 a2) :=
  is_equiv.mk inverse inverse inv_inv inv_inv (λp, eq.rec_on p idp)
  local attribute is_equiv_eq_inverse [instance]

  definition eq_equiv_eq_symm (a1 a2 : A) : (a1 = a2) ≃ (a2 = a1) :=
  equiv.mk inverse _

  definition is_equiv_concat_left [instance] (p : a1 = a2) (a3 : A)
    : is_equiv (@concat _ a1 a2 a3 p) :=
  is_equiv.mk (concat p) (concat p⁻¹)
              (con_inv_cancel_left p)
              (inv_con_cancel_left p)
              (eq.rec_on p (λq, eq.rec_on q idp))
  local attribute is_equiv_concat_left [instance]

  definition equiv_eq_closed_left (p : a1 = a2) (a3 : A) : (a1 = a3) ≃ (a2 = a3) :=
  equiv.mk (concat p⁻¹) _

  definition is_equiv_concat_right [instance] (p : a2 = a3) (a1 : A)
    : is_equiv (λq : a1 = a2, q ⬝ p) :=
  is_equiv.mk (λq, q ⬝ p) (λq, q ⬝ p⁻¹)
              (λq, inv_con_cancel_right q p)
              (λq, con_inv_cancel_right q p)
              (eq.rec_on p (λq, eq.rec_on q idp))
  local attribute is_equiv_concat_right [instance]

  definition equiv_eq_closed_right (p : a2 = a3) (a1 : A) : (a1 = a2) ≃ (a1 = a3) :=
  equiv.mk (λq, q ⬝ p) _

  definition eq_equiv_eq_closed (p : a1 = a2) (q : a3 = a4) : (a1 = a3) ≃ (a2 = a4) :=
  equiv.trans (equiv_eq_closed_left p a3) (equiv_eq_closed_right q a2)

  definition is_equiv_whisker_left (p : a1 = a2) (q r : a2 = a3)
  : is_equiv (@whisker_left A a1 a2 a3 p q r) :=
  begin
  fapply adjointify,
    {intro s, apply (!cancel_left s)},
    {intro s,
      apply concat, {apply whisker_left_con_right},
      apply concat, rotate_left 1, apply (whisker_left_inv_left p s),
      apply concat2,
        {apply concat, {apply whisker_left_con_right},
          apply concat2,
            {cases p, cases q, apply idp},
            {apply idp}},
        {cases p, cases r, apply idp}},
    {intro s, cases s, cases q, cases p, apply idp}
  end

  definition eq_equiv_con_eq_con_left (p : a1 = a2) (q r : a2 = a3) : (q = r) ≃ (p ⬝ q = p ⬝ r) :=
  equiv.mk _ !is_equiv_whisker_left

  definition is_equiv_whisker_right {p q : a1 = a2} (r : a2 = a3)
    : is_equiv (λs, @whisker_right A a1 a2 a3 p q s r) :=
  begin
  fapply adjointify,
    {intro s, apply (!cancel_right s)},
    {intro s, cases r, cases s, cases q, apply idp},
    {intro s, cases s, cases r, cases p, apply idp}
  end

  definition eq_equiv_con_eq_con_right (p q : a1 = a2) (r : a2 = a3) : (p = q) ≃ (p ⬝ r = q ⬝ r) :=
  equiv.mk _ !is_equiv_whisker_right

  definition is_equiv_con_eq_of_eq_inv_con (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : is_equiv (con_eq_of_eq_inv_con : p = r⁻¹ ⬝ q → r ⬝ p = q) :=
  begin
   cases r,
   apply (@is_equiv_compose _ _ _ _ _ !is_equiv_concat_left !is_equiv_concat_right),
  end

  definition eq_inv_con_equiv_con_eq (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : (p = r⁻¹ ⬝ q) ≃ (r ⬝ p = q) :=
  equiv.mk _ !is_equiv_con_eq_of_eq_inv_con

  definition is_equiv_con_eq_of_eq_con_inv (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : is_equiv (con_eq_of_eq_con_inv : r = q ⬝ p⁻¹ → r ⬝ p = q) :=
  begin
    cases p,
    apply (@is_equiv_compose _ _ _ _ _ !is_equiv_concat_left !is_equiv_concat_right)
  end

  definition eq_con_inv_equiv_con_eq (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : (r = q ⬝ p⁻¹) ≃ (r ⬝ p = q) :=
  equiv.mk _ !is_equiv_con_eq_of_eq_con_inv

  definition is_equiv_inv_con_eq_of_eq_con (p : a1 = a3) (q : a2 = a3) (r : a1 = a2)
    : is_equiv (inv_con_eq_of_eq_con : p = r ⬝ q → r⁻¹ ⬝ p = q) :=
  begin
    cases r,
    apply (@is_equiv_compose _ _ _ _ _ !is_equiv_concat_left !is_equiv_concat_right)
  end

  definition eq_con_equiv_inv_con_eq (p : a1 = a3) (q : a2 = a3) (r : a1 = a2)
    : (p = r ⬝ q) ≃ (r⁻¹ ⬝ p = q) :=
  equiv.mk _ !is_equiv_inv_con_eq_of_eq_con

  definition is_equiv_con_inv_eq_of_eq_con (p : a3 = a1) (q : a2 = a3) (r : a2 = a1)
    : is_equiv (con_inv_eq_of_eq_con : r = q ⬝ p → r ⬝ p⁻¹ = q) :=
  begin
    cases p,
    apply (@is_equiv_compose _ _ _ _ _ !is_equiv_concat_left !is_equiv_concat_right)
  end

  definition eq_con_equiv_con_inv_eq (p : a3 = a1) (q : a2 = a3) (r : a2 = a1)
    : (r = q ⬝ p) ≃ (r ⬝ p⁻¹ = q) :=
   equiv.mk _ !is_equiv_con_inv_eq_of_eq_con

  definition is_equiv_eq_con_of_inv_con_eq (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : is_equiv (eq_con_of_inv_con_eq : r⁻¹ ⬝ q = p → q = r ⬝ p) :=
  begin
    cases r,
    apply (@is_equiv_compose _ _ _ _ _ !is_equiv_concat_left !is_equiv_concat_right)
  end

  definition inv_con_eq_equiv_eq_con (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : (r⁻¹ ⬝ q = p) ≃ (q = r ⬝ p) :=
  equiv.mk _ !is_equiv_eq_con_of_inv_con_eq

  definition is_equiv_eq_con_of_con_inv_eq (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : is_equiv (eq_con_of_con_inv_eq : q ⬝ p⁻¹ = r → q = r ⬝ p) :=
  begin
    cases p,
    apply (@is_equiv_compose _ _ _ _ _ !is_equiv_concat_left !is_equiv_concat_right)
  end

  definition con_inv_eq_equiv_eq_con (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : (q ⬝ p⁻¹ = r) ≃ (q = r ⬝ p) :=
  equiv.mk _ !is_equiv_eq_con_of_con_inv_eq

  -- a lot of this library still needs to be ported from Coq HoTT

end eq
