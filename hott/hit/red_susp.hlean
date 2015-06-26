/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the reduced suspension
-/

import .two_quotient types.pointed algebra.e_closure

open simple_two_quotient eq unit pointed e_closure

namespace red_susp
section

  parameter {A : Pointed}

  inductive red_susp_R : unit → unit → Type :=
  | Rmk : Π(a : A), red_susp_R star star
  open red_susp_R
  inductive red_susp_Q : Π⦃x : unit⦄, e_closure red_susp_R x x → Type :=
  | Qmk : red_susp_Q [Rmk pt]
  open red_susp_Q
  local abbreviation R := red_susp_R
  local abbreviation Q := red_susp_Q

  definition red_susp : Type := simple_two_quotient R Q -- TODO: define this in root namespace

  definition base : red_susp :=
  incl0 R Q star

  definition merid (a : A) : base = base :=
  incl1 R Q (Rmk a)

  definition merid_pt : merid pt = idp :=
  incl2 R Q Qmk

  -- protected definition rec {P : red_susp → Type} (Pb : P base) (Pm : Π(a : A), Pb =[merid a] Pb)
  --   (Pe : Pm pt =[merid_pt] idpo) (x : red_susp) : P x :=
  -- begin
  --   induction x,
  -- end

  -- protected definition rec_on [reducible] {P : red_susp → Type} (x : red_susp) (Pb : P base)
  --   (Pm : Π(a : A), Pb =[merid a] Pb) (Pe : Pm pt =[merid_pt] idpo) : P x :=
  -- rec Pb Pm Pe x

  -- definition rec_merid {P : red_susp → Type} (Pb : P base) (Pm : Π(a : A), Pb =[merid a] Pb)
  --   (Pe : Pm pt =[merid_pt] idpo) (a : A)
  --   : apdo (rec Pb Pm Pe) (merid a) = Pm a :=
  -- !rec_incl1

  -- theorem elim_merid_pt {P : red_susp → Type} (Pb : P base) (Pm : Π(a : A), Pb =[merid a] Pb)
  --   (Pe : Pm pt =[merid_pt] idpo)
  --   : square (ap02 (rec Pb Pm Pe) merid_pt) Pe (rec_merid Pe pt) idp :=
  -- !rec_incl2

  protected definition elim {P : Type} (Pb : P) (Pm : Π(a : A), Pb = Pb)
    (Pe : Pm pt = idp) (x : red_susp) : P :=
  begin
    induction x,
      exact Pb,
      induction s, exact Pm a,
      induction q, exact Pe
  end

  protected definition elim_on [reducible] {P : Type} (x : red_susp) (Pb : P)
    (Pm : Π(a : A), Pb = Pb) (Pe : Pm pt = idp) : P :=
  elim Pb Pm Pe x

  definition elim_merid {P : Type} {Pb : P} {Pm : Π(a : A), Pb = Pb}
    (Pe : Pm pt = idp) (a : A)
    : ap (elim Pb Pm Pe) (merid a) = Pm a :=
  !elim_incl1

  theorem elim_merid_pt {P : Type} (Pb : P) (Pm : Π(a : A), Pb = Pb)
    (Pe : Pm pt = idp) : square (ap02 (elim Pb Pm Pe) merid_pt) Pe (elim_merid Pe pt) idp :=
  !elim_incl2

end
end red_susp

attribute red_susp.base [constructor]
attribute /-red_susp.rec-/ red_susp.elim [unfold-c 6] [recursor 6]
--attribute red_susp.elim_type [unfold-c 9]
attribute /-red_susp.rec_on-/ red_susp.elim_on [unfold-c 3]
--attribute red_susp.elim_type_on [unfold-c 6]
