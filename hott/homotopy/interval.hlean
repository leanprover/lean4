/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the interval
-/

import .susp types.eq types.prod cubical.square
open eq susp unit equiv is_trunc nat prod

definition interval : Type₀ := susp unit

namespace interval

  definition zero : interval := north
  definition one  : interval := south
  definition seg  : zero = one := merid star

  protected definition rec {P : interval → Type} (P0 : P zero) (P1 : P one)
    (Ps : P0 =[seg] P1) (x : interval) : P x :=
  begin
    fapply susp.rec_on x,
    { exact P0},
    { exact P1},
    { intro x, cases x, exact Ps}
  end

  protected definition rec_on [reducible] {P : interval → Type} (x : interval)
    (P0 : P zero) (P1 : P one) (Ps : P0 =[seg] P1) : P x :=
  interval.rec P0 P1 Ps x

  theorem rec_seg {P : interval → Type} (P0 : P zero) (P1 : P one) (Ps : P0 =[seg] P1)
      : apdo (interval.rec P0 P1 Ps) seg = Ps :=
  !rec_merid

  protected definition elim {P : Type} (P0 P1 : P) (Ps : P0 = P1) (x : interval) : P :=
  interval.rec P0 P1 (pathover_of_eq Ps) x

  protected definition elim_on [reducible] {P : Type} (x : interval) (P0 P1 : P)
    (Ps : P0 = P1) : P :=
  interval.elim P0 P1 Ps x

  theorem elim_seg {P : Type} (P0 P1 : P) (Ps : P0 = P1)
    : ap (interval.elim P0 P1 Ps) seg = Ps :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑interval.elim,rec_seg],
  end

  protected definition elim_type (P0 P1 : Type) (Ps : P0 ≃ P1) (x : interval) : Type :=
  interval.elim P0 P1 (ua Ps) x

  protected definition elim_type_on [reducible] (x : interval) (P0 P1 : Type) (Ps : P0 ≃ P1)
    : Type :=
  interval.elim_type P0 P1 Ps x

  theorem elim_type_seg (P0 P1 : Type) (Ps : P0 ≃ P1)
    : transport (interval.elim_type P0 P1 Ps) seg = Ps :=
  by rewrite [tr_eq_cast_ap_fn,↑interval.elim_type,elim_seg];apply cast_ua_fn

  definition is_contr_interval [instance] [priority 900] : is_contr interval :=
  is_contr.mk zero (λx, interval.rec_on x idp seg !pathover_eq_r_idp)

  open is_equiv equiv
  definition naive_funext_of_interval : naive_funext :=
  λA P f g p, ap (λ(i : interval) (x : A), interval.elim_on i (f x) (g x) (p x)) seg

end interval open interval

definition cube : ℕ → Type₀
| cube 0        := unit
| cube (succ n) := cube n × interval

abbreviation square := cube (succ (succ nat.zero))

definition cube_one_equiv_interval : cube 1 ≃ interval :=
!prod_comm_equiv ⬝e !prod_unit_equiv


definition prod_square {A B : Type} {a a' : A} {b b' : B} (p : a = a') (q : b = b')
  : square (pair_eq p idp) (pair_eq p idp) (pair_eq idp q) (pair_eq idp q) :=
by cases p; cases q; exact ids

namespace square

  definition tl : square := (star, zero, zero)
  definition tr : square := (star, one,  zero)
  definition bl : square := (star, zero, one )
  definition br : square := (star, one,  one )
  -- s stands for "square" in the following definitions
  definition st : tl = tr := pair_eq (pair_eq idp seg) idp
  definition sb : bl = br := pair_eq (pair_eq idp seg) idp
  definition sl : tl = bl := pair_eq idp seg
  definition sr : tr = br := pair_eq idp seg
  definition sfill : square st sb sl sr := !prod_square
  definition fill : st ⬝ sr = sl ⬝ sb := !square_equiv_eq sfill

end square
