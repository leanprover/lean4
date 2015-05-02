/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.option
Author: Leonardo de Moura
-/

import logic.eq
open eq.ops decidable

namespace option
  definition is_none {A : Type} (o : option A) : Prop :=
  option.rec true (λ a, false) o

  theorem is_none_none {A : Type} : is_none (@none A) :=
  trivial

  theorem not_is_none_some {A : Type} (a : A) : ¬ is_none (some a) :=
  not_false

  theorem none_ne_some {A : Type} (a : A) : none ≠ some a :=
  by contradiction

  theorem some.inj {A : Type} {a₁ a₂ : A} (H : some a₁ = some a₂) : a₁ = a₂ :=
  by injection H; assumption

  protected definition is_inhabited [instance] (A : Type) : inhabited (option A) :=
  inhabited.mk none

  protected definition has_decidable_eq [instance] {A : Type} [H : decidable_eq A] : decidable_eq (option A) :=
  take o₁ o₂ : option A,
    option.rec_on o₁
      (option.rec_on o₂ (inl rfl) (take a₂, (inr (none_ne_some a₂))))
      (take a₁ : A, option.rec_on o₂
        (inr (ne.symm (none_ne_some a₁)))
        (take a₂ : A, decidable.rec_on (H a₁ a₂)
          (assume Heq : a₁ = a₂, inl (Heq ▸ rfl))
          (assume Hne : a₁ ≠ a₂, inr (assume Hn : some a₁ = some a₂, absurd (some.inj Hn) Hne))))
end option
