/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the natural numbers specific to HoTT
-/

import .basic

open is_trunc unit empty eq equiv

namespace nat

  definition is_hprop_le [instance] (n m : ℕ) : is_hprop (n ≤ m) :=
  begin
    assert lem : Π{n m : ℕ} (p : n ≤ m) (q : n = m), p = q ▸ le.refl n,
    { intros, cases p,
      { assert H' : q = idp, apply is_hset.elim,
        cases H', reflexivity},
      { cases q, exfalso, apply not_succ_le_self a}},
    apply is_hprop.mk, intro H1 H2, induction H2,
    { apply lem},
    { cases H1,
      { exfalso, apply not_succ_le_self a},
      { exact ap le.step !v_0}},
  end
  definition le_equiv_succ_le_succ (n m : ℕ) : (n ≤ m) ≃ (succ n ≤ succ m) :=
  equiv_of_is_hprop succ_le_succ le_of_succ_le_succ
  definition le_succ_equiv_pred_le (n m : ℕ) : (n ≤ succ m) ≃ (pred n ≤ m) :=
  equiv_of_is_hprop pred_le_pred le_succ_of_pred_le


  -- definition is_hprop_lt [instance] (n m : ℕ) : is_hprop (n < m) :=
  -- begin
  --   assert H : Π{n m : ℕ} (p : n < m) (q : succ n = m), p = q ▸ lt.base n,
  --   { intros, cases p,
  --     { assert H' : q = idp, apply is_hset.elim,
  --       cases H', reflexivity},
  --     { cases q, exfalso, exact lt.irrefl b a}},
  --   apply is_hprop.mk, intros p q,
  --   induction q,
  --   { apply H},
  --   { cases p,
  --       exfalso, exact lt.irrefl b a,
  --       exact ap lt.step !v_0}
  -- end

  -- definition is_hprop_le (n m : ℕ) : is_hprop (n ≤ m) := !is_hprop_lt

end nat
