-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import data.nat.order logic.wf
open nat eq.ops

definition lt.wf [instance] : well_founded lt :=
well_founded.intro
 (take n, nat.induction_on n
    (acc.intro zero (λ (y : nat) (H : y < 0),
      absurd H !not_lt_zero))
    (λ (n : nat) (iH : acc lt n),
      acc.intro (succ n) (λ (m : nat) (H : m < succ n),
        have H₁ : m < n ∨ m = n, from le_imp_lt_or_eq (succ_le_cancel (lt_imp_le_succ H)),
        or.elim H₁
          (assume Hlt : m < n, acc.inv iH Hlt)
          (assume Heq : m = n, Heq⁻¹ ▸ iH))))
