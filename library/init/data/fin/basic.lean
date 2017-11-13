/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.basic
open nat
structure fin (n : nat) := (val : nat) (is_lt : val < n)

attribute [pp_using_anonymous_constructor] fin

namespace fin

protected def lt {n} (a b : fin n) : Prop :=
a.val < b.val

protected def le {n} (a b : fin n) : Prop :=
a.val ≤ b.val

instance {n} : has_lt (fin n)  := ⟨fin.lt⟩
instance {n} : has_le (fin n)  := ⟨fin.le⟩

instance decidable_lt {n} (a b : fin n) :  decidable (a < b) :=
nat.decidable_lt _ _

instance decidable_le {n} (a b : fin n) : decidable (a ≤ b) :=
nat.decidable_le _ _

def {u} elim0 {α : Sort u} : fin 0 → α
| ⟨_, h⟩ := absurd h (not_lt_zero _)

variable {n : nat}

lemma eq_of_veq : ∀ {i j : fin n}, (val i) = (val j) → i = j
| ⟨iv, ilt₁⟩ ⟨.(iv), ilt₂⟩ rfl := rfl

lemma veq_of_eq : ∀ {i j : fin n}, i = j → (val i) = (val j)
| ⟨iv, ilt⟩ .(_) rfl := rfl

lemma ne_of_vne {i j : fin n} (h : val i ≠ val j) : i ≠ j :=
λ h', absurd (veq_of_eq h') h

lemma vne_of_ne {i j : fin n} (h : i ≠ j) : val i ≠ val j :=
λ h', absurd (eq_of_veq h') h

end fin

open fin

instance (n : nat) : decidable_eq (fin n) :=
λ i j, decidable_of_decidable_of_iff
  (nat.decidable_eq i.val j.val) ⟨eq_of_veq, veq_of_eq⟩
