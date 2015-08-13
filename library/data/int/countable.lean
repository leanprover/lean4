/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.equiv data.int.basic data.encodable data.countable
open equiv bool sum

namespace int
definition int_equiv_bool_nat : int ≃ (bool × nat) :=
equiv.mk
  (λ i, match i with of_nat a := (tt, a) | neg_succ_of_nat a := (ff, a) end)
  (λ p, match p with (tt, a) := of_nat a | (ff, a) := neg_succ_of_nat a end)
  (λ i, begin cases i, repeat reflexivity end)
  (λ p, begin cases p with b a, cases b, repeat reflexivity end)

definition int_equiv_nat : int ≃ nat :=
calc int ≃ (bool × nat)                : int_equiv_bool_nat
     ... ≃ ((unit + unit) × nat)       : prod_congr bool_equiv_unit_sum_unit !_root_.equiv.refl
     ... ≃ (unit × nat) + (unit × nat) : sum_prod_distrib
     ... ≃ nat + nat                   : sum_congr !prod_unit_left !prod_unit_left
     ... ≃ nat                         : nat_sum_nat_equiv_nat

definition encodable_int [instance] : encodable int :=
encodable_of_equiv (_root_.equiv.symm int_equiv_nat)

lemma countable_int : countable int :=
countable_of_encodable encodable_int

end int
