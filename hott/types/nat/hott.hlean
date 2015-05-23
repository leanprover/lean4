/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the natural numbers specific to HoTT
-/

import .basic

open is_trunc unit empty eq

namespace nat

  definition is_hprop_lt [instance] (n m : ℕ) : is_hprop (n < m) :=
  begin
    assert H : Π{n m : ℕ} (p : n < m) (q : succ n = m), p = q ▸ lt.base n,
    { intros, cases p,
      { assert H' : q = idp, apply is_hset.elim,
        cases H', reflexivity},
      { cases q, exfalso, exact lt.irrefl b a}},
    apply is_hprop.mk, intros p q,
    induction q,
    { apply H},
    { cases p,
        exfalso, exact lt.irrefl b a,
        exact ap lt.step !v_0}
  end

  definition is_hprop_le (n m : ℕ) : is_hprop (n ≤ m) := !is_hprop_lt

end nat
