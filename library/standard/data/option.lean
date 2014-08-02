------------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------
import logic.connectives.basic logic.connectives.eq logic.classes.inhabited logic.classes.decidable
using eq_proofs decidable

namespace option
inductive option (A : Type) : Type :=
| none {} : option A
| some    : A → option A

theorem induction_on {A : Type} {p : option A → Prop} (o : option A) (H1 : p none) (H2 : ∀a, p (some a)) : p o :=
option_rec H1 H2 o

definition rec_on {A : Type} {C : option A → Type} (o : option A) (H1 : C none) (H2 : ∀a, C (some a)) : C o :=
option_rec H1 H2 o

definition is_none {A : Type} (o : option A) : Prop :=
option_rec true (λ a, false) o

theorem is_none_none {A : Type} : is_none (@none A) :=
trivial

theorem not_is_none_some {A : Type} (a : A) : ¬ is_none (some a) :=
not_false_trivial

theorem none_ne_some {A : Type} (a : A) : none ≠ some a :=
assume H : none = some a, absurd
  (H ▸ is_none_none)
  (not_is_none_some a)

theorem some_inj {A : Type} {a₁ a₂ : A} (H : some a₁ = some a₂) : a₁ = a₂ :=
congr2 (option_rec a₁ (λ a, a)) H

theorem inhabited_option [instance] (A : Type) : inhabited (option A) :=
inhabited_intro none

theorem decidable_eq [instance] {A : Type} {H : ∀a₁ a₂ : A, decidable (a₁ = a₂)} (o₁ o₂ : option A) : decidable (o₁ = o₂) :=
rec_on o₁
  (rec_on o₂ (inl (refl _)) (take a₂, (inr (none_ne_some a₂))))
  (take a₁ : A, rec_on o₂
    (inr (ne_symm (none_ne_some a₁)))
    (take a₂ : A, decidable.rec_on (H a₁ a₂)
      (assume Heq : a₁ = a₂, inl (Heq ▸ refl _))
      (assume Hne : a₁ ≠ a₂, inr (assume Hn : some a₁ = some a₂, absurd (some_inj Hn) Hne))))
end