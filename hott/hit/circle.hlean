/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.circle
Authors: Floris van Doorn

Declaration of the circle
-/

import .sphere

open eq suspension bool sphere_index equiv equiv.ops

definition circle [reducible] := sphere 1

namespace circle

  definition base1 : circle := !north
  definition base2 : circle := !south
  definition seg1 : base1 = base2 := merid !north
  definition seg2 : base1 = base2 := merid !south

  definition base : circle := base1
  definition loop : base = base := seg1 ⬝ seg2⁻¹

  definition rec2 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▹ Pb1 = Pb2) (Ps2 : seg2 ▹ Pb1 = Pb2) (x : circle) : P x :=
  begin
    fapply (suspension.rec_on x),
    { exact Pb1},
    { exact Pb2},
    { esimp, intro b, fapply (suspension.rec_on b),
      { exact Ps1},
      { exact Ps2},
      { intro x, cases x}},
  end

  definition rec2_on [reducible] {P : circle → Type} (x : circle) (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▹ Pb1 = Pb2) (Ps2 : seg2 ▹ Pb1 = Pb2) : P x :=
  circle.rec2 Pb1 Pb2 Ps1 Ps2 x

  theorem rec2_seg1 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▹ Pb1 = Pb2) (Ps2 : seg2 ▹ Pb1 = Pb2)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  !rec_merid

  theorem rec2_seg2 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▹ Pb1 = Pb2) (Ps2 : seg2 ▹ Pb1 = Pb2)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  !rec_merid

  definition elim2 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2) (x : circle) : P :=
  rec2 Pb1 Pb2 (!tr_constant ⬝ Ps1) (!tr_constant ⬝ Ps2) x

  definition elim2_on [reducible] {P : Type} (x : circle) (Pb1 Pb2 : P)
    (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2) : P :=
  elim2 Pb1 Pb2 Ps1 Ps2 x

  theorem elim2_seg1 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2)
    : ap (elim2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant seg1 (elim2 Pb1 Pb2 Ps1 Ps2 base1))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim2,rec2_seg1],
  end

  theorem elim2_seg2 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2)
    : ap (elim2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant seg2 (elim2 Pb1 Pb2 Ps1 Ps2 base1))),
    rewrite [-apd_eq_tr_constant_con_ap,↑elim2,rec2_seg2],
  end

  protected definition rec {P : circle → Type} (Pbase : P base) (Ploop : loop ▹ Pbase = Pbase)
    (x : circle) : P x :=
  begin
    fapply (rec2_on x),
    { exact Pbase},
    { exact (transport P seg1 Pbase)},
    { apply idp},
    { apply tr_eq_of_eq_inv_tr, exact (Ploop⁻¹ ⬝ !con_tr)},
  end
--rewrite -tr_con, exact Ploop⁻¹

  protected definition rec_on [reducible] {P : circle → Type} (x : circle) (Pbase : P base)
    (Ploop : loop ▹ Pbase = Pbase) : P x :=
  rec Pbase Ploop x

  theorem rec_loop_helper {A : Type} (P : A → Type)
    {x y : A} {p : x = y} {u : P x} {v : P y} (q : u = p⁻¹ ▹ v) :
    eq_inv_tr_of_tr_eq (tr_eq_of_eq_inv_tr q) = q :=
  by cases p; exact idp

  definition con_refl {A : Type} {x y : A} (p : x = y) : p ⬝ refl _ = p :=
  eq.rec_on p idp

  theorem rec_loop {P : circle → Type} (Pbase : P base) (Ploop : loop ▹ Pbase = Pbase) :
    apd (rec Pbase Ploop) loop = Ploop :=
  begin
    rewrite [↑loop,apd_con,↑rec,↑rec2_on,↑base,rec2_seg1,apd_inv,rec2_seg2,↑ap], --con_idp should work here
    apply concat, apply (ap (λx, x ⬝ _)), apply con_idp, esimp,
    rewrite [rec_loop_helper,inv_con_inv_left],
    apply con_inv_cancel_left
  end

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
