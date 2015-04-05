/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.suspension
Authors: Floris van Doorn

Declaration of suspension and spheres
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
    (Pmerid : Π(a : A), merid a ▹ PN = PS) (x : suspension A) : P x :=
  begin
    fapply (pushout.rec_on _ _ x),
    { intro u, cases u, exact PN},
    { intro u, cases u, exact PS},
    { exact Pmerid},
  end

  protected definition rec_on {A : Type} {P : suspension A → Type} (y : suspension A)
    (PN : P !north) (PS : P !south) (Pmerid : Π(a : A), merid a ▹ PN = PS) : P y :=
  rec PN PS Pmerid y

end suspension

open nat suspension bool

definition sphere (n : ℕ) := nat.rec_on n bool (λk Sk, suspension Sk)
definition circle [reducible] := sphere 1

namespace circle

  definition base : circle := !north
  definition loop : base = base := merid tt ⬝ (merid ff)⁻¹

  protected definition rec2 {P : circle → Type} (PN : P !north) (PS : P !south)
    (Pff : merid ff ▹ PN = PS) (Ptt : merid tt ▹ PN = PS) (x : circle) : P x :=
  begin
    fapply (suspension.rec_on x),
    { exact PN},
    { exact PS},
    { intro b, cases b, exact Pff, exact Ptt},
  end

  protected definition rec2_on {P : circle → Type} (x : circle) (PN : P !north) (PS : P !south)
    (Pff : merid ff ▹ PN = PS) (Ptt : merid tt ▹ PN = PS) : P x :=
  circle.rec2 PN PS Pff Ptt x

  protected definition rec {P : circle → Type} (Pbase : P base) (Ploop : loop ▹ Pbase = Pbase)
    (x : circle) : P x :=
  begin
    fapply (rec2_on x),
    { exact Pbase},
    { sexact (merid ff ▹ Pbase)},
    { apply idp},
    { apply eq_tr_of_inv_tr_eq, rewrite -tr_con, apply Ploop},
  end

  protected definition rec_on {P : circle → Type} (x : circle) (Pbase : P base)
    (Ploop : loop ▹ Pbase = Pbase) : P x :=
  circle.rec Pbase Ploop x

  protected definition rec_constant {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    (x : circle) : P :=
  circle.rec Pbase (tr_constant loop Pbase ⬝ Ploop) x

  definition comp_loop {P : circle → Type} (Pbase : P base) (Ploop : loop ▹ Pbase = Pbase) :
    ap (circle.rec Pbase Ploop) loop = sorry ⬝ Ploop ⬝ sorry :=
  sorry

  definition comp_constant_loop {P : Type} (Pbase : P) (Ploop : Pbase = Pbase) :
    ap (circle.rec_constant Pbase Ploop) loop = sorry ⬝ Ploop ⬝ sorry :=
  sorry


  protected definition rec_on_constant {P : Type} (x : circle) (Pbase : P) (Ploop : Pbase = Pbase)
     : P :=
  rec_constant Pbase Ploop x

end circle
