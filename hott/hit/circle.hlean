/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the circle
-/

import .sphere types.bool types.eq types.int.hott types.arrow types.equiv algebra.fundamental_group algebra.hott

open eq suspension bool sphere_index is_equiv equiv equiv.ops is_trunc

definition circle : Type₀ := sphere 1

namespace circle
  notation `S¹` := circle
  definition base1 : circle := !north
  definition base2 : circle := !south
  definition seg1 : base1 = base2 := merid !north
  definition seg2 : base1 = base2 := merid !south

  definition base : circle := base1
  definition loop : base = base := seg1 ⬝ seg2⁻¹

  definition rec2 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▸ Pb1 = Pb2) (Ps2 : seg2 ▸ Pb1 = Pb2) (x : circle) : P x :=
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
    (Ps1 : seg1 ▸ Pb1 = Pb2) (Ps2 : seg2 ▸ Pb1 = Pb2) : P x :=
  circle.rec2 Pb1 Pb2 Ps1 Ps2 x

  theorem rec2_seg1 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▸ Pb1 = Pb2) (Ps2 : seg2 ▸ Pb1 = Pb2)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  !rec_merid

  theorem rec2_seg2 {P : circle → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : seg1 ▸ Pb1 = Pb2) (Ps2 : seg2 ▸ Pb1 = Pb2)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  !rec_merid

  definition elim2 {P : Type} (Pb1 Pb2 : P) (Ps1 Ps2 : Pb1 = Pb2) (x : circle) : P :=
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

  definition elim2_type (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2) (x : circle) : Type :=
  elim2 Pb1 Pb2 (ua Ps1) (ua Ps2) x

  definition elim2_type_on [reducible] (x : circle) (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2)
    : Type :=
  elim2_type Pb1 Pb2 Ps1 Ps2 x

  theorem elim2_type_seg1 (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2)
    : transport (elim2_type Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  by rewrite [tr_eq_cast_ap_fn,↑elim2_type,elim2_seg1];apply cast_ua_fn

  theorem elim2_type_seg2 (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2)
    : transport (elim2_type Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  by rewrite [tr_eq_cast_ap_fn,↑elim2_type,elim2_seg2];apply cast_ua_fn

  protected definition rec {P : circle → Type} (Pbase : P base) (Ploop : loop ▸ Pbase = Pbase)
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
    (Ploop : loop ▸ Pbase = Pbase) : P x :=
  circle.rec Pbase Ploop x

  theorem rec_loop_helper {A : Type} (P : A → Type)
    {x y : A} {p : x = y} {u : P x} {v : P y} (q : u = p⁻¹ ▸ v) :
    eq_inv_tr_of_tr_eq (tr_eq_of_eq_inv_tr q) = q :=
  by cases p; exact idp

  definition con_refl {A : Type} {x y : A} (p : x = y) : p ⬝ refl _ = p :=
  eq.rec_on p idp

  theorem rec_loop {P : circle → Type} (Pbase : P base) (Ploop : loop ▸ Pbase = Pbase) :
    apd (circle.rec Pbase Ploop) loop = Ploop :=
  begin
    rewrite [↑loop,apd_con,↑circle.rec,↑circle.rec2_on,↑base,rec2_seg1,apd_inv,rec2_seg2,↑ap], --con_idp should work here
    apply concat, apply (ap (λx, x ⬝ _)), apply con_idp, esimp,
    rewrite [rec_loop_helper,inv_con_inv_left],
    apply con_inv_cancel_left
  end

  protected definition elim {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    (x : circle) : P :=
  circle.rec Pbase (tr_constant loop Pbase ⬝ Ploop) x

  protected definition elim_on [reducible] {P : Type} (x : circle) (Pbase : P)
    (Ploop : Pbase = Pbase) : P :=
  circle.elim Pbase Ploop x

  theorem elim_loop {P : Type} (Pbase : P) (Ploop : Pbase = Pbase) :
    ap (circle.elim Pbase Ploop) loop = Ploop :=
  begin
    apply (@cancel_left _ _ _ _ (tr_constant loop (circle.elim Pbase Ploop base))),
    rewrite [-apd_eq_tr_constant_con_ap,↑circle.elim,rec_loop],
  end

  protected definition elim_type (Pbase : Type) (Ploop : Pbase ≃ Pbase)
    (x : circle) : Type :=
  circle.elim Pbase (ua Ploop) x

  protected definition elim_type_on [reducible] (x : circle) (Pbase : Type)
    (Ploop : Pbase ≃ Pbase) : Type :=
  circle.elim_type Pbase Ploop x

  theorem elim_type_loop (Pbase : Type) (Ploop : Pbase ≃ Pbase) :
    transport (circle.elim_type Pbase Ploop) loop = Ploop :=
  by rewrite [tr_eq_cast_ap_fn,↑circle.elim_type,circle.elim_loop];apply cast_ua_fn

  theorem elim_type_loop_inv (Pbase : Type) (Ploop : Pbase ≃ Pbase) :
    transport (circle.elim_type Pbase Ploop) loop⁻¹ = to_inv Ploop :=
  by rewrite [tr_inv_fn,↑to_inv]; apply inv_eq_inv; apply elim_type_loop
end circle

attribute circle.base circle.base1 circle.base2 [constructor]
attribute circle.rec circle.elim [unfold-c 4]
attribute circle.elim_type [unfold-c 3]
attribute circle.rec_on circle.elim_on [unfold-c 2]
attribute circle.elim_type_on [unfold-c 1]
attribute circle.rec2 circle.elim2 [unfold-c 6]
attribute circle.elim2_type [unfold-c 5]
attribute circle.rec2_on circle.elim2_on [unfold-c 2]
attribute circle.elim2_type [unfold-c 1]

namespace circle
  definition pointed_circle [instance] [constructor] : pointed circle :=
  pointed.mk base

  definition loop_neq_idp : loop ≠ idp :=
  assume H : loop = idp,
  have H2 : Π{A : Type₁} {a : A} (p : a = a), p = idp,
    from λA a p, calc
      p   = ap (circle.elim a p) loop : elim_loop
      ... = ap (circle.elim a p) (refl base) : by rewrite H,
  absurd !H2 eq_bnot_ne_idp

  definition nonidp (x : circle) : x = x :=
  circle.rec_on x loop
    (calc
      loop ▸ loop = loop⁻¹ ⬝ loop ⬝ loop : transport_eq_lr
        ... = loop : by rewrite [con.left_inv, idp_con])

  definition nonidp_neq_idp : nonidp ≠ (λx, idp) :=
  assume H : nonidp = λx, idp,
  have H2 : loop = idp, from apd10 H base,
  absurd H2 loop_neq_idp

  open int

  protected definition code (x : circle) : Type₀ :=
  circle.elim_type_on x ℤ equiv_succ

  definition transport_code_loop (a : ℤ) : transport circle.code loop a = succ a :=
  ap10 !elim_type_loop a

  definition transport_code_loop_inv (a : ℤ)
    : transport circle.code loop⁻¹ a = pred a :=
  ap10 !elim_type_loop_inv a

  protected definition encode {x : circle} (p : base = x) : circle.code x :=
  transport circle.code p (of_num 0) -- why is the explicit coercion needed here?

  protected definition decode {x : circle} : circle.code x → base = x :=
  begin
    refine circle.rec_on x _ _,
    { exact power loop},
    { apply eq_of_homotopy, intro a,
      refine !arrow.arrow_transport ⬝ !transport_eq_r ⬝ _,
      rewrite [transport_code_loop_inv,power_con,succ_pred]}
  end

  --remove this theorem after #484
  theorem encode_decode {x : circle} : Π(a : circle.code x), circle.encode (circle.decode a) = a :=
  begin
    unfold circle.decode, refine circle.rec_on x _ _,
    { intro a, esimp [base,base1], --simplify after #587
      apply rec_nat_on a,
      { exact idp},
      { intros n p,
        apply transport (λ(y : base = base), transport circle.code y _ = _), apply power_con,
        rewrite [▸*,con_tr, transport_code_loop, ↑[circle.encode,circle.code] at p, p]},
      { intros n p,
        apply transport (λ(y : base = base), transport circle.code y _ = _),
        { exact !power_con_inv ⬝ ap (power loop) !neg_succ⁻¹},
        rewrite [▸*,@con_tr _ circle.code,transport_code_loop_inv, ↑[circle.encode] at p, p, -neg_succ]}},
    { apply eq_of_homotopy, intro a, apply @is_hset.elim, esimp [circle.code,base,base1], exact _}
        --simplify after #587
  end


  definition circle_eq_equiv (x : circle) : (base = x) ≃ circle.code x :=
  begin
    fapply equiv.MK,
    { exact circle.encode},
    { exact circle.decode},
    { exact circle.encode_decode},
    { intro p, cases p, exact idp},
  end

  definition base_eq_base_equiv : base = base ≃ ℤ :=
  circle_eq_equiv base

  definition decode_add (a b : ℤ) :
    base_eq_base_equiv⁻¹ a ⬝ base_eq_base_equiv⁻¹ b = base_eq_base_equiv⁻¹ (a + b) :=
  !power_con_power

  definition encode_con (p q : base = base) : circle.encode (p ⬝ q) = circle.encode p + circle.encode q :=
  preserve_binary_of_inv_preserve base_eq_base_equiv concat add decode_add p q

  --the carrier of π₁(S¹) is the set-truncation of base = base.
  open core algebra trunc equiv.ops
  definition fg_carrier_equiv_int : π₁(S¹) ≃ ℤ :=
  trunc_equiv_trunc 0 base_eq_base_equiv ⬝e !equiv_trunc⁻¹ᵉ

  definition fundamental_group_of_circle : π₁(S¹) = group_integers :=
  begin
    apply (Group_eq fg_carrier_equiv_int),
    intros g h,
    apply trunc.rec_on g, intro g', apply trunc.rec_on h, intro h',
    -- esimp at *,
    -- esimp [fg_carrier_equiv_int,equiv.trans,equiv.symm,equiv_trunc,trunc_equiv_trunc,
    --   base_eq_base_equiv,circle_eq_equiv,is_equiv_tr,semigroup.to_has_mul,monoid.to_semigroup,
    --   group.to_monoid,fundamental_group.mul],
    apply encode_con,
  end

end circle
