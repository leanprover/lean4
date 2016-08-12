/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.monad init.alternative

open decidable

attribute [instance]
definition option_is_inhabited (A : Type) : inhabited (option A) :=
inhabited.mk none

attribute [instance]
definition option_has_decidable_eq {A : Type} [H : decidable_eq A] : ∀ o₁ o₂ : option A, decidable (o₁ = o₂)
| none      none      := tt rfl
| none      (some v₂) := ff (λ H, option.no_confusion H)
| (some v₁) none      := ff (λ H, option.no_confusion H)
| (some v₁) (some v₂) :=
  match (H v₁ v₂) with
  | (tt e) := tt (congr_arg (@some A) e)
  | (ff n) := ff (λ H, option.no_confusion H (λ e, absurd e n))
  end

attribute [inline]
definition option_fmap {A B : Type} (f : A → B) (e : option A) : option B :=
option.cases_on e
  none
  (λ a, some (f a))

attribute [inline]
definition option_bind {A B : Type} (a : option A) (b : A → option B) : option B :=
option.cases_on a
  none
  (λ a, b a)

attribute [instance]
definition option_is_monad : monad option :=
monad.mk @option_fmap @some @option_bind

definition option_orelse {A : Type} : option A → option A → option A
| (some a) _         := some a
| none     (some a)  := some a
| none     none      := none

attribute [instance]
definition option_is_alternative {A : Type} : alternative option :=
alternative.mk @option_fmap @some (@fapp _ _) @none @option_orelse

definition optionT (m : Type → Type) [monad m] (A : Type) :=
m (option A)

attribute [inline]
definition optionT_fmap {m : Type → Type} [monad m] {A B : Type} (f : A → B) (e : optionT m A) : optionT m B :=
@monad.bind m _ _ _ e (λ a : option A, option.cases_on a (return none) (λ a, return (some (f a))))

attribute [inline]
definition optionT_bind {m : Type → Type} [monad m] {A B : Type} (a : optionT m A) (b : A → optionT m B)
                               : optionT m B :=
@monad.bind m _ _ _ a (λ a : option A, option.cases_on a (return none) (λ a, b a))

attribute [inline]
definition optionT_return {m : Type → Type} [monad m] {A : Type} (a : A) : optionT m A :=
@monad.ret m _ _ (some a)

attribute [instance]
definition optionT_is_monad {m : Type → Type} [monad m] {A : Type} : monad (optionT m) :=
monad.mk (@optionT_fmap m _) (@optionT_return m _) (@optionT_bind m _)

definition optionT_orelse {m : Type → Type} [monad m] {A : Type} (a : optionT m A) (b : optionT m A) : optionT m A :=
@monad.bind m _ _ _ a (λ a : option A, option.cases_on a b (λ a, return (some a)))

definition optionT_fail {m : Type → Type} [monad m] {A : Type} : optionT m A :=
@monad.ret m _ _ none

attribute [instance]
definition optionT_is_alternative {m : Type → Type} [monad m] {A : Type} : alternative (optionT m) :=
alternative.mk
  (@optionT_fmap m _)
  (@optionT_return m _)
  (@fapp (optionT m) (@optionT_is_monad m _ A))
  (@optionT_fail m _)
  (@optionT_orelse m _)
