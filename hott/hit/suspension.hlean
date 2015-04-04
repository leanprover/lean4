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
    (Pmerid : Π(a : A), merid a ▹ PN = PS) (y : suspension A) : P y :=
  begin
    fapply (pushout.rec_on _ _ y),
    { intro u, cases u, exact PN},
    { intro u, cases u, exact PS},
    { exact Pmerid},
  end

  protected definition rec_on {A : Type} {P : suspension A → Type} (y : suspension A)
    (PN : P !north) (PS : P !south) (Pmerid : Π(a : A), merid a ▹ PN = PS) : P y :=
  rec PN PS Pmerid y

end suspension
