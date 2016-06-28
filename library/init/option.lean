/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Basic datatypes
-/
prelude
import init.logic init.monad

open decidable

definition option_is_inhabited [instance] (A : Type) : inhabited (option A) :=
inhabited.mk none

definition option_has_decidable_eq [instance] {A : Type} [H : decidable_eq A] : ∀ o₁ o₂ : option A, decidable (o₁ = o₂)
| none      none      := tt rfl
| none      (some v₂) := ff (λ H, option.no_confusion H)
| (some v₁) none      := ff (λ H, option.no_confusion H)
| (some v₁) (some v₂) :=
  match H v₁ v₂ with
  | tt e := tt (congr_arg (@some A) e)
  | ff n := ff (λ H, option.no_confusion H (λ e, absurd e n))
  end

namespace option
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
