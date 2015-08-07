/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Theorems about the booleans
-/

open is_equiv eq equiv function is_trunc option unit

namespace bool

  definition ff_ne_tt : ff = tt → empty
  | [none]

  definition is_equiv_bnot [instance] [priority 500] : is_equiv bnot :=
  begin
    fapply is_equiv.mk,
      exact bnot,
      all_goals (intro b;cases b), do 6 reflexivity
--      all_goals (focus (intro b;cases b;all_goals reflexivity)),
  end

  definition equiv_bnot : bool ≃ bool := equiv.mk bnot _
  definition eq_bnot    : bool = bool := ua equiv_bnot

  definition eq_bnot_ne_idp : eq_bnot ≠ idp :=
  assume H : eq_bnot = idp,
  assert H2 : bnot = id, from !cast_ua_fn⁻¹ ⬝ ap cast H,
  absurd (ap10 H2 tt) ff_ne_tt


  definition bool_equiv_option_unit : bool ≃ option unit :=
  begin
    fapply equiv.MK,
    { intro b, cases b, exact none, exact some star},
    { intro u, cases u, exact ff, exact tt},
    { intro u, cases u with u, reflexivity, cases u, reflexivity},
    { intro b, cases b, reflexivity, reflexivity},
  end
end bool
