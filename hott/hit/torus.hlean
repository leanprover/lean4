/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of the torus
-/

import .two_quotient

open two_quotient eq bool unit relation

namespace torus

  definition torus_R (x y : unit) := bool
  local infix `⬝r`:75 := @e_closure.trans unit torus_R star star star
  local postfix `⁻¹ʳ`:(max+10) := @e_closure.symm unit torus_R star star
  local notation `[`:max a `]`:0 := @e_closure.of_rel unit torus_R star star a

  inductive torus_Q : Π⦃x y : unit⦄, e_closure torus_R x y → e_closure torus_R x y → Type :=
  | Qmk : torus_Q ([ff] ⬝r [tt]) ([tt] ⬝r [ff])

  definition torus := two_quotient torus_R torus_Q
  definition base  : torus := incl0 _ _ star
  definition loop1 : base = base := incl1 _ _ ff
  definition loop2 : base = base := incl1 _ _ tt
  definition surf  : loop1 ⬝ loop2 = loop2 ⬝ loop1 :=
  incl2 _ _ torus_Q.Qmk

  -- protected definition rec {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   (x : torus) : P x :=
  -- sorry

  -- example {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb) (Pl2 : Pb =[loop2] Pb)
  --         (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2) : torus.rec Pb Pl1 Pl2 Pf base = Pb := idp

  -- definition rec_loop1 {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   : apdo (torus.rec Pb Pl1 Pl2 Pf) loop1 = Pl1 :=
  -- sorry

  -- definition rec_loop2 {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   : apdo (torus.rec Pb Pl1 Pl2 Pf) loop2 = Pl2 :=
  -- sorry

  -- definition rec_surf {P : torus → Type} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
  --   (Pl2 : Pb =[loop2] Pb) (Pf : squareover P fill Pl1 Pl1 Pl2 Pl2)
  --   : cubeover P rfl1 (apds (torus.rec Pb Pl1 Pl2 Pf) fill) Pf
  --              (vdeg_squareover !rec_loop2) (vdeg_squareover !rec_loop2)
  --              (vdeg_squareover !rec_loop1) (vdeg_squareover !rec_loop1) :=
  -- sorry

  protected definition elim {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : Pl1 ⬝ Pl2 = Pl2 ⬝ Pl1) (x : torus) : P :=
  begin
    induction x,
    { exact Pb},
    { induction s,
      { exact Pl1},
      { exact Pl2}},
    { induction q, exact Ps},
  end

  protected definition elim_on [reducible] {P : Type} (x : torus) (Pb : P)
    (Pl1 : Pb = Pb) (Pl2 : Pb = Pb) (Ps : Pl1 ⬝ Pl2 = Pl2 ⬝ Pl1) : P :=
  torus.elim Pb Pl1 Pl2 Ps x

  definition elim_loop1 {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : Pl1 ⬝ Pl2 = Pl2 ⬝ Pl1) : ap (torus.elim Pb Pl1 Pl2 Ps) loop1 = Pl1 :=
  !elim_incl1

  definition elim_loop2 {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : Pl1 ⬝ Pl2 = Pl2 ⬝ Pl1) : ap (torus.elim Pb Pl1 Pl2 Ps) loop2 = Pl2 :=
  !elim_incl1

  definition elim_surf {P : Type} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : Pl1 ⬝ Pl2 = Pl2 ⬝ Pl1)
  : square (ap02 (torus.elim Pb Pl1 Pl2 Ps) surf)
           Ps
           (!ap_con ⬝ (!elim_loop1 ◾ !elim_loop2))
           (!ap_con ⬝ (!elim_loop2 ◾ !elim_loop1)) :=
  !elim_incl2

end torus

attribute torus.base [constructor]
attribute /-torus.rec-/ torus.elim [unfold-c 6] [recursor 6]
--attribute torus.elim_type [unfold-c 9]
attribute /-torus.rec_on-/ torus.elim_on [unfold-c 2]
--attribute torus.elim_type_on [unfold-c 6]
