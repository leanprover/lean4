/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.monad init.alternative
set_option new_elaborator true
open decidable

universe variables u v

attribute [instance]
definition option_is_inhabited (A : Type u) : inhabited (option A) :=
inhabited.mk none

attribute [instance]
definition option_has_decidable_eq {A : Type u} [H : decidable_eq A] : ∀ o₁ o₂ : option A, decidable (o₁ = o₂)
| none      none      := is_true rfl
| none      (some v₂) := is_false (λ H, option.no_confusion H)
| (some v₁) none      := is_false (λ H, option.no_confusion H)
| (some v₁) (some v₂) :=
  match (H v₁ v₂) with
  | (is_true e)  := is_true (congr_arg (@some A) e)
  | (is_false n) := is_false (λ H, option.no_confusion H (λ e, absurd e n))
  end

attribute [inline]
definition option_fmap {A : Type} {B : Type} (f : A → B) : option A → option B
| none     := none
| (some a) := some (f a)

attribute [inline]
definition option_bind {A : Type} {B : Type} : option A → (A → option B) → option B
| none     b := none
| (some a) b := b a

attribute [instance]
definition option_is_monad : monad option :=
monad.mk @option_fmap @some @option_bind

definition option_orelse {A : Type} : option A → option A → option A
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

attribute [instance]
definition option_is_alternative {A : Type} : alternative option :=
alternative.mk @option_fmap @some (@fapp _ _) @none @option_orelse

definition optionT (m : Type → Type) [monad m] (A : Type) :=
m (option A)

attribute [inline]
definition optionT_fmap {m : Type → Type} [monad m] {A B : Type} (f : A → B) (e : optionT m A) : optionT m B :=
show m (option B), from
do o ← e,
   match o with
   | none     := return none
   | (some a) := return (some (f a))
   end

attribute [inline]
definition optionT_bind {m : Type → Type} [monad m] {A B : Type} (a : optionT m A) (b : A → optionT m B)
                               : optionT m B :=
show m (option B), from
do o ← a,
   match o with
   | none     := return none
   | (some a) := b a
   end

attribute [inline]
definition optionT_return {m : Type → Type} [monad m] {A : Type} (a : A) : optionT m A :=
show m (option A), from
return (some a)

attribute [instance]
definition optionT_is_monad {m : Type → Type} [monad m] {A : Type} : monad (optionT m) :=
monad.mk (@optionT_fmap m _) (@optionT_return m _) (@optionT_bind m _)

definition optionT_orelse {m : Type → Type} [monad m] {A : Type} (a : optionT m A) (b : optionT m A) : optionT m A :=
show m (option A), from
do o ← a,
   match o with
   | none     := b
   | (some v) := return (some v)
   end

definition optionT_fail {m : Type → Type} [monad m] {A : Type} : optionT m A :=
show m (option A), from
return none

attribute [instance]
definition optionT_is_alternative {m : Type → Type} [monad m] {A : Type} : alternative (optionT m) :=
alternative.mk
  (@optionT_fmap m _)
  (@optionT_return m _)
  (@fapp (optionT m) (@optionT_is_monad m _ A))
  (@optionT_fail m _)
  (@optionT_orelse m _)
