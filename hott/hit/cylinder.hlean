/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.cylinder
Authors: Floris van Doorn

Declaration of mapping cylinders
-/

import .colimit

open colimit bool unit eq

namespace cylinder
context

universe u
parameters {A B : Type.{u}} (f : A → B)

  definition cylinder_diag [reducible] : diagram :=
  diagram.mk bool
             unit.{0}
             (λi, bool.rec_on i A B)
             (λj, ff)
             (λj, tt)
             (λj, f)

  local notation `D` := cylinder_diag

  definition cylinder := colimit cylinder_diag -- TODO: define this in root namespace
  local attribute cylinder_diag [instance]

  definition base (b : B) : cylinder :=
  @ι _ _ b

  definition top (a : A) : cylinder :=
  @ι _ _ a

  definition seg (a : A) : base (f a) = top a :=
  @cglue _ star a

  protected definition rec {P : cylinder → Type}
    (Pbase : Π(b : B), P (base b)) (Ptop : Π(a : A), P (top a))
    (Pseg : Π(a : A), seg a ▹ Pbase (f a) = Ptop a) (x : cylinder) : P x :=
  begin
    fapply (@colimit.rec_on _ _ x),
    { intros [i, x], cases i,
        apply Ptop,
        apply Pbase},
    { intros [j, x], cases j, apply Pseg}
  end

  protected definition rec_on [reducible] {P : cylinder → Type} (x : cylinder)
    (Pbase : Π(b : B), P (base b)) (Ptop  : Π(a : A), P (top a))
    (Pseg  : Π(a : A), seg a ▹ Pbase (f a) = Ptop a) : P x :=
  rec Pbase Ptop Pseg x

  protected definition elim {P : Type} (Pbase : B → P) (Ptop : A → P)
    (Pseg : Π(a : A), Pbase (f a) = Ptop a) (x : cylinder) : P :=
  rec Pbase Ptop (λa, !tr_constant ⬝ Pseg a) x

  protected definition elim_on [reducible] {P : Type} (x : cylinder) (Pbase : B → P) (Ptop : A → P)
    (Pseg : Π(a : A), Pbase (f a) = Ptop a) : P :=
  elim Pbase Ptop Pseg x

  definition rec_seg {P : cylinder → Type}
    (Pbase : Π(b : B), P (base b)) (Ptop : Π(a : A), P (top a))
    (Pseg : Π(a : A), seg a ▹ Pbase (f a) = Ptop a)
      (a : A) : apD (rec Pbase Ptop Pseg) (seg a) = sorry ⬝ Pseg a ⬝ sorry :=
  sorry

  definition elim_seg {P : Type} (Pbase : B → P) (Ptop : A → P)
    (Pseg : Π(a : A), Pbase (f a) = Ptop a)
    (a : A) : ap (elim Pbase Ptop Pseg) (seg a) = sorry ⬝ Pseg a ⬝ sorry :=
  sorry

end

end cylinder
