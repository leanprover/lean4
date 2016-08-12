/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.nat
open nat

structure fin (n : nat) := (val : nat) (is_lt : val < n)

namespace fin

variable {n : nat}

set_option pp.all true

lemma eq_of_veq : ∀ {i j : fin n}, (val i) = (val j) → i = j
| (mk iv ilt) (mk jv jlt) := assume (veq : iv = jv),
  have ∀ e : iv = jv, mk iv ilt = mk jv (eq.subst e ilt), from
    eq.rec_on veq (λ e : iv = iv, (eq.refl (mk iv (eq.subst e ilt)))),
  this veq

lemma veq_of_eq : ∀ {i j : fin n}, i = j → (val i) = (val j)
| (mk iv ilt) (mk jv jlt) := assume Peq,
  show iv = jv, from fin.no_confusion Peq (λ Pe Pqe, Pe)

lemma eq_iff_veq {i j : fin n} : (val i) = (val j) ↔ i = j :=
iff.intro eq_of_veq veq_of_eq

end fin

open decidable fin

attribute [instance]
protected definition fin.has_decidable_eq (n : nat) : ∀ (i j : fin n), decidable (i = j)
| (mk ival ilt) (mk jval jlt) :=
  decidable_of_decidable_of_iff (nat.has_decidable_eq ival jval) eq_iff_veq
