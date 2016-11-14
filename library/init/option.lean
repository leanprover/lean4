/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.monad init.alternative
open decidable

universe variables u v

instance (A : Type u) : inhabited (option A) :=
⟨none⟩

instance {A : Type u} [H : decidable_eq A] : decidable_eq (option A)
| none      none      := is_true rfl
| none      (some v₂) := is_false (λ H, option.no_confusion H)
| (some v₁) none      := is_false (λ H, option.no_confusion H)
| (some v₁) (some v₂) :=
  match (H v₁ v₂) with
  | (is_true e)  := is_true (congr_arg (@some A) e)
  | (is_false n) := is_false (λ H, option.no_confusion H (λ e, absurd e n))
  end

@[inline] def option_fmap {A : Type u} {B : Type v} (f : A → B) : option A → option B
| none     := none
| (some a) := some (f a)

@[inline] def option_bind {A : Type u} {B : Type v} : option A → (A → option B) → option B
| none     b := none
| (some a) b := b a

instance : monad option :=
monad.mk @option_fmap @some @option_bind

def option_orelse {A : Type u} : option A → option A → option A
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

instance {A : Type u} : alternative option :=
alternative.mk @option_fmap @some (@fapp _ _) @none @option_orelse

def optionT (M : Type (max 1 u) → Type v) [monad M] (A : Type u) : Type v :=
M (option A)

@[inline] def optionT_fmap {M : Type (max 1 u) → Type v} [monad M] {A B : Type u} (f : A → B) (e : optionT M A) : optionT M B :=
show M (option B), from
do o ← e,
   match o with
   | none     := return none
   | (some a) := return (some (f a))
   end

@[inline] def optionT_bind {M : Type (max 1 u) → Type v} [monad M] {A B : Type u} (a : optionT M A) (b : A → optionT M B)
                               : optionT M B :=
show M (option B), from
do o ← a,
   match o with
   | none     := return none
   | (some a) := b a
   end

@[inline] def optionT_return {M : Type (max 1 u) → Type v} [monad M] {A : Type u} (a : A) : optionT M A :=
show M (option A), from
return (some a)

instance {M : Type (max 1 u) → Type v} [monad M] : monad (optionT M) :=
monad.mk (@optionT_fmap M _) (@optionT_return M _) (@optionT_bind M _)

def optionT_orelse {M : Type (max 1 u) → Type v} [monad M] {A : Type u} (a : optionT M A) (b : optionT M A) : optionT M A :=
show M (option A), from
do o ← a,
   match o with
   | none     := b
   | (some v) := return (some v)
   end

def optionT_fail {M : Type (max 1 u) → Type v} [monad M] {A : Type u} : optionT M A :=
show M (option A), from
return none

instance {M : Type (max 1 u) → Type v} [monad M] : alternative (optionT M) :=
{map     := @optionT_fmap M _,
 pure    := @optionT_return M _,
 seq     := @fapp (optionT M) (@optionT.monad M _),
 failure := @optionT_fail M _,
 orelse  := @optionT_orelse M _}
