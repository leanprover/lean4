/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core init.control.monad init.control.alternative init.coe
open decidable

universes u v

namespace option

def to_monad {m : Type → Type} [monad m] [alternative m] {A} : option A → m A
| none := failure
| (some a) := pure a

def get_or_else {α : Type u} : option α → α → α
| (some x) _ := x
| none     e := e

def get {α : Type u} [inhabited α] : option α → α
| (some x) := x
| none     := default α

def to_bool {α : Type u} : option α → bool
| (some _) := tt
| none     := ff

def is_some {α : Type u} : option α → bool
| (some _) := tt
| none     := ff

def is_none {α : Type u} : option α → bool
| (some _) := ff
| none     := tt

@[inline] protected def bind {α : Type u} {β : Type v} : option α → (α → option β) → option β
| none     b := none
| (some a) b := b a

protected def map {α β} (f : α → β) (o : option α) : option β :=
option.bind o (some ∘ f)

theorem map_id {α} : (option.map id : option α → option α) = id :=
funext (λo, match o with | none := rfl | some x := rfl)

instance : monad option :=
{pure := @some, bind := @option.bind, map := @option.map}

protected def orelse {α : Type u} : option α → option α → option α
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

instance : alternative option :=
{ failure := @none,
  orelse  := @option.orelse,
  ..option.monad }

protected def lt {α : Type u} (r : α → α → Prop) : option α → option α → Prop
| none (some x)     := true
| (some x) (some y) := r x y
| _ _               := false

instance decidable_rel_lt {α : Type u} (r : α → α → Prop) [s : decidable_rel r] : decidable_rel (option.lt r)
| none     (some y) := is_true  trivial
| (some x) (some y) := s x y
| (some x) none     := is_false not_false
| none     none     := is_false not_false

end option

instance (α : Type u) : inhabited (option α) :=
⟨none⟩

instance {α : Type u} [decidable_eq α] : decidable_eq (option α) :=
{dec_eq := λ a b, match a, b with
 | none,      none      := is_true rfl
 | none,      (some v₂) := is_false (λ h, option.no_confusion h)
 | (some v₁), none      := is_false (λ h, option.no_confusion h)
 | (some v₁), (some v₂) :=
   match dec_eq v₁ v₂ with
   | (is_true e)  := is_true (congr_arg (@some α) e)
   | (is_false n) := is_false (λ h, option.no_confusion h (λ e, absurd e n))}

instance {α : Type u} [has_lt α] : has_lt (option α) := ⟨option.lt (<)⟩
