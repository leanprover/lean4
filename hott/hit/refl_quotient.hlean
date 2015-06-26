/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Quotient of a reflexive relation
-/

import hit.circle types.cubical.squareover .two_quotient

open eq simple_two_quotient e_closure

namespace refl_quotient
section

  parameters {A : Type} (R : A → A → Type) (ρ : Πa, R a a)
  inductive refl_quotient_Q : Π⦃a : A⦄, e_closure R a a → Type :=
  | Qmk {} : Π(a : A), refl_quotient_Q [ρ a]
  open refl_quotient_Q
  local abbreviation Q := refl_quotient_Q

  definition refl_quotient : Type := simple_two_quotient R Q -- TODO: define this in root namespace

  definition rclass_of (a : A) : refl_quotient := incl0 R Q a
  definition req_of_rel ⦃a a' : A⦄ (r : R a a') : rclass_of a = rclass_of a' :=
  incl1 R Q r

  definition pρ (a : A) : req_of_rel (ρ a) = idp :=
  incl2 R Q (Qmk a)

  -- protected definition rec {P : refl_quotient → Type}
  --   (Pc : Π(a : A), P (rclass_of a))
  --   (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
  --   (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo)
  --   (x : refl_quotient) : P x :=
  -- sorry

  -- protected definition rec_on [reducible] {P : refl_quotient → Type}
  --   (Pc : Π(a : A), P (rclass_of a))
  --   (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
  --   (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo) : P y :=
  -- rec Pinl Pinr Pglue y

  -- definition rec_req_of_rel {P : Type} {P : refl_quotient → Type}
  --   (Pc : Π(a : A), P (rclass_of a))
  --   (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
  --   (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo)
  --   ⦃a a' : A⦄ (r : R a a') : apdo (rec Pc Pp Pr) (req_of_rel r) = Pp r :=
  -- !rec_incl1

  -- theorem rec_pρ {P : Type} {P : refl_quotient → Type}
  --   (Pc : Π(a : A), P (rclass_of a))
  --   (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
  --   (Pr : Π(a : A), Pp (ρ a) =[pρ a] idpo) (a : A)
  --    : square (ap02 (rec Pc Pp Pr) (pρ a)) (Pr a) (elim_req_of_rel Pr (ρ a)) idp :=
  -- !rec_incl2

  protected definition elim {P : Type} (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp)
    (x : refl_quotient) : P :=
  begin
    induction x,
      exact Pc a,
      exact Pp s,
      induction q, apply Pr
  end

  protected definition elim_on [reducible] {P : Type} (x : refl_quotient) (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp) : P :=
  elim Pc Pp Pr x

  definition elim_req_of_rel {P : Type} {Pc : Π(a : A), P}
    {Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a'} (Pr : Π(a : A), Pp (ρ a) = idp)
    ⦃a a' : A⦄ (r : R a a') : ap (elim Pc Pp Pr) (req_of_rel r) = Pp r :=
  !elim_incl1

  theorem elim_pρ {P : Type} (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp) (a : A)
     : square (ap02 (elim Pc Pp Pr) (pρ a)) (Pr a) (elim_req_of_rel Pr (ρ a)) idp :=
  !elim_incl2

end
end refl_quotient

attribute refl_quotient.rclass_of [constructor]
attribute /-refl_quotient.rec-/ refl_quotient.elim [unfold-c 8] [recursor 8]
--attribute refl_quotient.elim_type [unfold-c 9]
attribute /-refl_quotient.rec_on-/ refl_quotient.elim_on [unfold-c 5]
--attribute refl_quotient.elim_type_on [unfold-c 6]
