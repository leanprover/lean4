/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.coeq
Authors: Floris van Doorn

Declaration of the coequalizer
-/

import .type_quotient

open type_quotient eq equiv equiv.ops

namespace coeq
section

universe u
parameters {A B : Type.{u}} (f g : A → B)

  inductive coeq_rel : B → B → Type :=
  | Rmk : Π(x : A), coeq_rel (f x) (g x)
  open coeq_rel
  local abbreviation R := coeq_rel

  definition coeq : Type := type_quotient coeq_rel -- TODO: define this in root namespace

  definition coeq_i (x : B) : coeq :=
  class_of R x

  /- cp is the name Coq uses. I don't know what it abbreviates, but at least it's short :-) -/
  definition cp (x : A) : coeq_i (f x) = coeq_i (g x) :=
  eq_of_rel coeq_rel (Rmk f g x)

  protected definition rec {P : coeq → Type} (P_i : Π(x : B), P (coeq_i x))
    (Pcp : Π(x : A), cp x ▸ P_i (f x) = P_i (g x)) (y : coeq) : P y :=
  begin
    fapply (type_quotient.rec_on y),
    { intro a, apply P_i},
    { intro a a' H, cases H, apply Pcp}
  end

  protected definition rec_on [reducible] {P : coeq → Type} (y : coeq)
    (P_i : Π(x : B), P (coeq_i x)) (Pcp : Π(x : A), cp x ▸ P_i (f x) = P_i (g x)) : P y :=
  rec P_i Pcp y

  theorem rec_cp {P : coeq → Type} (P_i : Π(x : B), P (coeq_i x))
    (Pcp : Π(x : A), cp x ▸ P_i (f x) = P_i (g x))
      (x : A) : apd (rec P_i Pcp) (cp x) = Pcp x :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (P_i : B → P)
    (Pcp : Π(x : A), P_i (f x) = P_i (g x)) (y : coeq) : P :=
  rec P_i (λx, !tr_constant ⬝ Pcp x) y

  protected definition elim_on [reducible] {P : Type} (y : coeq) (P_i : B → P)
    (Pcp : Π(x : A), P_i (f x) = P_i (g x)) : P :=
  elim P_i Pcp y

  theorem elim_cp {P : Type} (P_i : B → P) (Pcp : Π(x : A), P_i (f x) = P_i (g x))
    (x : A) : ap (elim P_i Pcp) (cp x) = Pcp x :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant (cp x) (elim P_i Pcp (coeq_i (f x))))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim,rec_cp],
  end

  protected definition elim_type (P_i : B → Type)
    (Pcp : Π(x : A), P_i (f x) ≃ P_i (g x)) (y : coeq) : Type :=
  elim P_i (λx, ua (Pcp x)) y

  protected definition elim_type_on [reducible] (y : coeq) (P_i : B → Type)
    (Pcp : Π(x : A), P_i (f x) ≃ P_i (g x)) : Type :=
  elim_type P_i Pcp y

  theorem elim_type_cp (P_i : B → Type) (Pcp : Π(x : A), P_i (f x) ≃ P_i (g x))
    (x : A) : transport (elim_type P_i Pcp) (cp x) = Pcp x :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_cp];apply cast_ua_fn

end

end coeq

attribute coeq.coeq_i [constructor]
attribute coeq.rec coeq.elim [unfold-c 8]
attribute coeq.elim_type [unfold-c 7]
attribute coeq.rec_on coeq.elim_on [unfold-c 6]
attribute coeq.elim_type_on [unfold-c 5]
