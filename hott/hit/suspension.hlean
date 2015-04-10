/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.suspension
Authors: Floris van Doorn

Declaration of suspension
-/

import .pushout

open pushout unit eq

definition suspension (A : Type) : Type := pushout (λ(a : A), star) (λ(a : A), star)

namespace suspension

  definition north (A : Type) : suspension A :=
  inl _ _ star

  definition south (A : Type) : suspension A :=
  inr _ _ star

  definition merid {A : Type} (a : A) : north A = south A :=
  glue _ _ a

  protected definition rec {A : Type} {P : suspension A → Type} (PN : P !north) (PS : P !south)
    (Pm : Π(a : A), merid a ▹ PN = PS) (x : suspension A) : P x :=
  begin
    fapply (pushout.rec_on _ _ x),
    { intro u, cases u, exact PN},
    { intro u, cases u, exact PS},
    { exact Pm},
  end

  protected definition rec_on [reducible] {A : Type} {P : suspension A → Type} (y : suspension A)
    (PN : P !north) (PS : P !south) (Pm : Π(a : A), merid a ▹ PN = PS) : P y :=
  rec PN PS Pm y

  definition rec_merid {A : Type} {P : suspension A → Type} (PN : P !north) (PS : P !south)
    (Pm : Π(a : A), merid a ▹ PN = PS) (a : A)
      : apD (rec PN PS Pm) (merid a) = sorry ⬝ Pm a ⬝ sorry :=
  sorry

  protected definition elim {A : Type} {P : Type} (PN : P) (PS : P) (Pm : A → PN = PS)
    (x : suspension A) : P :=
  rec PN PS (λa, !tr_constant ⬝ Pm a) x

  protected definition elim_on [reducible] {A : Type} {P : Type} (x : suspension A)
    (PN : P) (PS : P)  (Pm : A → PN = PS) : P :=
  elim PN PS Pm x

  protected definition elim_merid {A : Type} {P : Type} (PN : P) (PS : P) (Pm : A → PN = PS)
    (x : suspension A) (a : A) : ap (elim PN PS Pm) (merid a) = sorry ⬝ Pm a ⬝ sorry :=
  sorry

end suspension
