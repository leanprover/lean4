/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

import logic.eq
open eq.ops decidable

namespace option
  definition is_none {A : Type} : option A →  Prop
  | none     := true
  | (some v) := false

  theorem is_none_none {A : Type} : is_none (@none A) :=
  trivial

  theorem not_is_none_some {A : Type} (a : A) : ¬ is_none (some a) :=
  not_false

  theorem none_ne_some {A : Type} (a : A) : none ≠ some a :=
  sorry -- by contradiction

  theorem some.inj {A : Type} {a₁ a₂ : A} (H : some a₁ = some a₂) : a₁ = a₂ :=
  sorry -- by injection H; assumption

  protected definition is_inhabited [instance] (A : Type) : inhabited (option A) :=
  inhabited.mk none

  protected definition has_decidable_eq [instance] {A : Type} [H : decidable_eq A] : ∀ o₁ o₂ : option A, decidable (o₁ = o₂)
  | none      none      := tt sorry -- by left;  reflexivity
  | none      (some v₂) := ff sorry -- by right; contradiction
  | (some v₁) none      := ff sorry -- by right; contradiction
  | (some v₁) (some v₂) :=
    match H v₁ v₂ with
    | tt e := tt sorry -- by left; congruence; assumption
    | ff n := ff sorry -- by right; intro h; injection h; contradiction
    end

  inline protected definition fmap {A B : Type} (f : A → B) (e : option A) : option B :=
  option.cases_on e
    none
    (λ a, some (f a))

  inline protected definition bind {A B : Type} (a : option A) (b : A → option B) : option B :=
  option.cases_on a
    none
    (λ a, b a)

  inline protected definition return {A : Type} (a : A) : option A :=
  some a

end option

definition option.is_monad [instance] : monad option :=
monad.mk @option.fmap @option.return @option.bind
