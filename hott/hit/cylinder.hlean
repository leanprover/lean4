/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.cylinder
Authors: Floris van Doorn

Mapping cylinders
-/

/- The hit mapping cylinder is primitive, declared in init.hit. -/

open eq

namespace cylinder

  variables {A B : Type} {f : A → B}

  protected definition elim {P : Type} (Pbase : B → P) (Ptop  : A → P)
    (Pseg  : Π(a : A), Ptop a = Pbase (f a)) {b : B} (x : cylinder f b) : P :=
  cylinder.rec Pbase Ptop (λa, !tr_constant ⬝ Pseg a) x

  protected definition elim_on [reducible] {P : Type} {b : B} (x : cylinder f b)
    (Pbase : B → P) (Ptop : A → P)
    (Pseg  : Π(a : A), Ptop a = Pbase (f a)) : P :=
  cylinder.elim Pbase Ptop Pseg x

  definition elim_seg {P : Type} (Pbase : B → P) (Ptop  : A → P)
    (Pseg  : Π(a : A), Ptop a = Pbase (f a)) {b : B} (x : cylinder f b) (a : A) :
      ap (elim Pbase Ptop Pseg) (seg f a) = sorry ⬝ Pseg a ⬝ sorry :=
  sorry

end cylinder
