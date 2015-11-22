/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of the torus
-/

import hit.two_quotient

open two_quotient eq bool unit equiv

namespace torus

  open e_closure relation
  definition torus_R (x y : unit) := bool
  local infix `⬝r`:75 := @e_closure.trans unit torus_R star star star
  local postfix `⁻¹ʳ`:(max+10) := @e_closure.symm unit torus_R star star
  local notation `[`:max a `]`:0 := @e_closure.of_rel unit torus_R star star a

  inductive torus_Q : Π⦃x y : unit⦄, e_closure torus_R x y → e_closure torus_R x y → Type :=
  | Qmk : torus_Q ([ff] ⬝r [tt]) ([tt] ⬝r [ff])

  open torus_Q

  definition torus := two_quotient torus_R torus_Q
  notation `T²` := torus
  definition base  : torus := incl0 _ _ star
  definition loop1 : base = base := incl1 _ _ ff
  definition loop2 : base = base := incl1 _ _ tt
  definition surf' : loop1 ⬝ loop2 = loop2 ⬝ loop1 :=
  incl2 _ _ Qmk
  definition surf  : square loop1 loop1 loop2 loop2 :=
  square_of_eq (incl2 _ _ Qmk)

  protected definition rec {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Ps : squareover P surf Pl1 Pl1 Pl2 Pl2) (x : torus) : P x :=
  begin
    induction x,
    { induction a, exact Pb},
    { induction s: induction a; induction a',
      { exact Pl1},
      { exact Pl2}},
    { induction q, esimp, apply change_path_of_pathover, apply pathover_of_squareover, exact Ps},
  end

  protected definition rec_on [reducible] {P : torus → Type} (x : torus) (Pb : P base)
    (Pl1 : Pb =[loop1] Pb) (Pl2 : Pb =[loop2] Pb) (Ps : squareover P surf Pl1 Pl1 Pl2 Pl2) : P x :=
  torus.rec Pb Pl1 Pl2 Ps x

  theorem rec_loop1 {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Ps : squareover P surf Pl1 Pl1 Pl2 Pl2)
    : apdo (torus.rec Pb Pl1 Pl2 Ps) loop1 = Pl1 :=
  !rec_incl1

  theorem rec_loop2 {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Ps : squareover P surf Pl1 Pl1 Pl2 Pl2)
    : apdo (torus.rec Pb Pl1 Pl2 Ps) loop2 = Pl2 :=
  !rec_incl1

  protected definition elim {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : square Pl1 Pl1 Pl2 Pl2) (x : torus) : P :=
  begin
    induction x,
    { exact Pb},
    { induction s,
      { exact Pl1},
      { exact Pl2}},
    { induction q, apply eq_of_square, exact Ps},
  end

  protected definition elim_on [reducible] {P : Type} (x : torus) (Pb : P)
    (Pl1 : Pb = Pb) (Pl2 : Pb = Pb) (Ps : square Pl1 Pl1 Pl2 Pl2) : P :=
  torus.elim Pb Pl1 Pl2 Ps x

  definition elim_loop1 {P : Type} {Pb : P} {Pl1 : Pb = Pb} {Pl2 : Pb = Pb}
    (Ps : square Pl1 Pl1 Pl2 Pl2) : ap (torus.elim Pb Pl1 Pl2 Ps) loop1 = Pl1 :=
  !elim_incl1

  definition elim_loop2 {P : Type} {Pb : P} {Pl1 : Pb = Pb} {Pl2 : Pb = Pb}
    (Ps : square Pl1 Pl1 Pl2 Pl2) : ap (torus.elim Pb Pl1 Pl2 Ps) loop2 = Pl2 :=
  !elim_incl1

  theorem elim_surf {P : Type} {Pb : P} {Pl1 : Pb = Pb} {Pl2 : Pb = Pb}
    (Ps : square Pl1 Pl1 Pl2 Pl2)
    : whisker_square (elim_loop1 Ps) (elim_loop1 Ps) (elim_loop2 Ps) (elim_loop2 Ps)
                     (aps (torus.elim Pb Pl1 Pl2 Ps) surf) = Ps :=
  begin
    apply whisker_square_aps_eq,
    apply elim_incl2
  end

end torus

attribute torus.base [constructor]
attribute torus.rec torus.elim [unfold 6] [recursor 6]
--attribute torus.elim_type [unfold 5]
attribute torus.rec_on torus.elim_on [unfold 2]
--attribute torus.elim_type_on [unfold 1]
