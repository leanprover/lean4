-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import data.nat.order logic.wf
open nat eq.ops

namespace nat

inductive pred_rel : nat → nat → Prop :=
intro : Π (n : nat), pred_rel n (succ n)

definition not_pred_rel_zero (n : nat) : ¬ pred_rel n zero :=
have aux : ∀{m}, pred_rel n m → succ n = m, from
  λm H, pred_rel.rec_on H (take n, rfl),
assume H : pred_rel n zero,
  absurd (aux H) !succ_ne_zero

definition pred_rel_succ {a b : nat} (H : pred_rel a (succ b)) : b = a :=
have aux : pred (succ b) = a, from
  pred_rel.rec_on H (λn, rfl),
aux

-- Predecessor relation is well-founded
definition pred_rel.wf : well_founded pred_rel :=
well_founded.intro
  (λn, induction_on n
    (acc.intro zero (λy (H : pred_rel y zero), absurd H (not_pred_rel_zero y)))
    (λa (iH : acc pred_rel a),
       acc.intro (succ a) (λy (H : pred_rel y (succ a)),
         have aux : a = y, from pred_rel_succ H,
         eq.rec_on aux iH)))

-- Less-than relation is well-founded
definition lt.wf [instance] : well_founded lt :=
well_founded.intro
 (λn, induction_on n
    (acc.intro zero (λ (y : nat) (H : y < 0),
      absurd H !not_lt_zero))
    (λ (n : nat) (iH : acc lt n),
      acc.intro (succ n) (λ (m : nat) (H : m < succ n),
        have H₁ : m < n ∨ m = n, from le_imp_lt_or_eq (succ_le_cancel (lt_imp_le_succ H)),
        or.elim H₁
          (assume Hlt : m < n, acc.inv iH Hlt)
          (assume Heq : m = n, Heq⁻¹ ▸ iH))))

definition measure {A : Type} (f : A → nat) : A → A → Prop :=
inv_image lt f

definition measure.wf {A : Type} (f : A → nat) : well_founded (measure f) :=
inv_image.wf f lt.wf

end nat
