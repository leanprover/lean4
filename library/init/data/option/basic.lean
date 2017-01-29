/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.category
open decidable

universe variables u v

namespace option

def to_monad {m : Type → Type} [monad m] [alternative m] {A} : option A → m A
| none := failure
| (some a) := return a

def get_or_else {α : Type u} : option α → α → α
| (some x) _ := x
| none     e := e

def is_some {α : Type u} : option α → bool
| (some _) := tt
| none     := ff

end option

instance (α : Type u) : inhabited (option α) :=
⟨none⟩

instance {α : Type u} [d : decidable_eq α] : decidable_eq (option α)
| none      none      := is_true rfl
| none      (some v₂) := is_false (λ h, option.no_confusion h)
| (some v₁) none      := is_false (λ h, option.no_confusion h)
| (some v₁) (some v₂) :=
  match (d v₁ v₂) with
  | (is_true e)  := is_true (congr_arg (@some α) e)
  | (is_false n) := is_false (λ h, option.no_confusion h (λ e, absurd e n))
  end

@[inline] def option_fmap {α : Type u} {β : Type v} (f : α → β) : option α → option β
| none     := none
| (some a) := some (f a)

@[inline] def option_bind {α : Type u} {β : Type v} : option α → (α → option β) → option β
| none     b := none
| (some a) b := b a

instance : monad option :=
{map := @option_fmap, ret := @some, bind := @option_bind}

def option_orelse {α : Type u} : option α → option α → option α
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

instance {α : Type u} : alternative option :=
alternative.mk @option_fmap @some (@fapp _ _) @none @option_orelse

def option_t (m : Type u → Type v) [monad m] (α : Type u) : Type v :=
m (option α)

@[inline] def option_t_fmap {m : Type u → Type v} [monad m] {α β : Type u} (f : α → β) (e : option_t m α) : option_t m β :=
show m (option β), from
do o ← e,
   match o with
   | none     := return none
   | (some a) := return (some (f a))
   end

@[inline] def option_t_bind {m : Type u → Type v} [monad m] {α β : Type u} (a : option_t m α) (b : α → option_t m β)
                               : option_t m β :=
show m (option β), from
do o ← a,
   match o with
   | none     := return none
   | (some a) := b a
   end

@[inline] def option_t_return {m : Type u → Type v} [monad m] {α : Type u} (a : α) : option_t m α :=
show m (option α), from
return (some a)

instance {m : Type u → Type v} [monad m] : monad (option_t m) :=
{map := @option_t_fmap m _, ret := @option_t_return m _, bind := @option_t_bind m _}

def option_t_orelse {m : Type u → Type v} [monad m] {α : Type u} (a : option_t m α) (b : option_t m α) : option_t m α :=
show m (option α), from
do o ← a,
   match o with
   | none     := b
   | (some v) := return (some v)
   end

def option_t_fail {m : Type u → Type v} [monad m] {α : Type u} : option_t m α :=
show m (option α), from
return none

instance {m : Type u → Type v} [monad m] : alternative (option_t m) :=
{map     := @option_t_fmap m _,
 pure    := @option_t_return m _,
 seq     := @fapp (option_t m) (@option_t.monad m _),
 failure := @option_t_fail m _,
 orelse  := @option_t_orelse m _}
