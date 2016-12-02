/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.basic
open nat
structure fin (n : nat) := (val : nat) (is_lt : val < n)

namespace fin

variable {n : nat}

lemma eq_of_veq : ∀ {i j : fin n}, (val i) = (val j) → i = j
| ⟨iv, ilt₁⟩ ⟨.iv, ilt₂⟩ rfl := rfl

lemma veq_of_eq : ∀ {i j : fin n}, i = j → (val i) = (val j)
| ⟨iv, ilt⟩ .⟨iv, ilt⟩ rfl := rfl

lemma ne_of_vne {i j : fin n} (h : val i ≠ val j) : i ≠ j :=
λ h', absurd (veq_of_eq h') h

lemma vne_of_ne {i j : fin n} (h : i ≠ j) : val i ≠ val j :=
λ h', absurd (eq_of_veq h') h

end fin

open fin

instance (n : nat) : decidable_eq (fin n)
| ⟨ival, ilt⟩ ⟨jval, jlt⟩ :=
  match nat.decidable_eq ival jval with
  | is_true  h₁ := is_true (eq_of_veq h₁)
  | is_false h₁ := is_false (λ h₂, absurd (veq_of_eq h₂) h₁)
  end
