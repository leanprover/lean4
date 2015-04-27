/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.circle
Authors: Floris van Doorn

Declaration of the circle
-/

import .sphere

open eq suspension bool sphere_index equiv equiv.ops

definition circle [reducible] := suspension bool --redefine this as sphere 1

namespace circle

  definition base1 : circle := !north
  definition base2 : circle := !south
  definition seg1 : base1 = base2 := merid tt
  definition seg2 : base2 = base1 := (merid ff)⁻¹

  definition base : circle := base1
  definition loop : base = base := seg1 ⬝ seg2

  definition rec2 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▹ Pb1 = Pb2) (Ps2 : seg2 ▹ Pb2 = Pb1) (x : circle) : P x :=
  begin
    fapply (suspension.rec_on x),
    { exact Pb1},
    { exact Pb2},
    { intro b, cases b,
        apply tr_eq_of_eq_inv_tr, exact Ps2⁻¹,
        exact Ps1},
  end

  definition rec2_on [reducible] {P : circle → Type} (x : circle) (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▹ Pb1 = Pb2) (Ps2 : seg2 ▹ Pb2 = Pb1) : P x :=
  circle.rec2 Pb1 Pb2 Ps1 Ps2 x

  theorem rec2_seg1 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▹ Pb1 = Pb2) (Ps2 : seg2 ▹ Pb2 = Pb1)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  sorry

  theorem rec2_seg2 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▹ Pb1 = Pb2) (Ps2 : seg2 ▹ Pb2 = Pb1)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  sorry

  definition elim2 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb2 = Pb1) (x : circle) : P :=
  rec2 Pb1 Pb2 (!tr_constant ⬝ Ps1) (!tr_constant ⬝ Ps2) x

  definition elim2_on [reducible] {P : Type} (x : circle) (Pb1 Pb2 : P)
    (Ps1 : Pb1 = Pb2) (Ps2 : Pb2 = Pb1) : P :=
  elim2 Pb1 Pb2 Ps1 Ps2 x

  theorem elim2_seg1 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb2 = Pb1)
    : ap (elim2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant seg1 (elim2 Pb1 Pb2 Ps1 Ps2 base1))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim2,rec2_seg1],
  end

  theorem elim2_seg2 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb2 = Pb1)
    : ap (elim2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant seg2 (elim2 Pb1 Pb2 Ps1 Ps2 base2))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim2,rec2_seg2],
  end

  protected definition rec {P : circle → Type} (Pbase : P base) (Ploop : loop ▹ Pbase = Pbase)
    (x : circle) : P x :=
  begin
    fapply (rec2_on x),
    { exact Pbase},
    { exact (transport P seg1 Pbase)},
    { apply idp},
    { apply eq_tr_of_inv_tr_eq, rewrite -tr_con, apply Ploop},
  end

  example {P : circle → Type} (Pbase : P base) (Ploop : loop ▹ Pbase = Pbase) : rec Pbase Ploop base = Pbase := idp

  protected definition rec_on [reducible] {P : circle → Type} (x : circle) (Pbase : P base)
    (Ploop : loop ▹ Pbase = Pbase) : P x :=
  rec Pbase Ploop x

  theorem rec_loop {P : circle → Type} (Pbase : P base) (Ploop : loop ▹ Pbase = Pbase) :
    apd (rec Pbase Ploop) loop = Ploop :=
  sorry

  protected definition elim {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    (x : circle) : P :=
  rec Pbase (tr_constant loop Pbase ⬝ Ploop) x

  protected definition elim_on [reducible] {P : Type} (x : circle) (Pbase : P)
    (Ploop : Pbase = Pbase) : P :=
  elim Pbase Ploop x

  theorem elim_loop {P : Type} (Pbase : P) (Ploop : Pbase = Pbase) :
    ap (elim Pbase Ploop) loop = Ploop :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant loop (elim Pbase Ploop base))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim,rec_loop],
  end

  protected definition elim_type (Pbase : Type) (Ploop : Pbase ≃ Pbase)
    (x : circle) : Type :=
  elim Pbase (ua Ploop) x

  protected definition elim_type_on [reducible] (x : circle) (Pbase : Type)
    (Ploop : Pbase ≃ Pbase) : Type :=
  elim_type Pbase Ploop x

  theorem elim_type_loop (Pbase : Type) (Ploop : Pbase ≃ Pbase) :
    transport (elim_type Pbase Ploop) loop = Ploop :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_loop];apply cast_ua_fn

end circle
