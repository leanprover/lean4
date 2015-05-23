/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Theorems about the booleans
-/

open is_equiv eq equiv function is_trunc

namespace bool

  definition ff_ne_tt : ff = tt → empty
  | [none]

  definition is_equiv_bnot [instance] [priority 500] : is_equiv bnot :=
  begin
    fapply is_equiv.mk,
      exact bnot,
      do 3 focus (intro b;cases b;all_goals (exact idp))
      --should information be propagated with all_goals?
      -- all_goals (intro b;cases b),
      -- all_goals (exact idp)
--      all_goals (focus (intro b;cases b;all_goals (exact idp))),
  end

  definition equiv_bnot : bool ≃ bool := equiv.mk bnot _
  definition eq_bnot    : bool = bool := ua equiv_bnot

  definition eq_bnot_ne_idp : eq_bnot ≠ idp :=
  assume H : eq_bnot = idp,
  assert H2 : bnot = id, from !cast_ua_fn⁻¹ ⬝ ap cast H,
  absurd (ap10 H2 tt) ff_ne_tt

  definition not_is_hset_type : ¬is_hset Type₀ :=
  assume H : is_hset Type₀,
  absurd !is_hset.elim eq_bnot_ne_idp
end bool
