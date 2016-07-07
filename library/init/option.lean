/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Basic datatypes
-/
prelude
import init.logic init.monad init.alternative

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

inline definition option_fmap {A B : Type} (f : A → B) (e : option A) : option B :=
option.cases_on e
  none
  (λ a, some (f a))

inline definition option_bind {A B : Type} (a : option A) (b : A → option B) : option B :=
option.cases_on a
  none
  (λ a, b a)

definition option_is_monad [instance] : monad option :=
monad.mk @option_fmap @some @option_bind

definition option_orelse {A : Type} : option A → option A → option A
| (some a) _         := some a
| none     (some a)  := some a
| none     none      := none

definition option_is_alternative [instance] {A : Type} : alternative option :=
alternative.mk @option_fmap @some (@fapp _ _) @none @option_orelse
