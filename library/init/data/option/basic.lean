/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.category.monad init.category.alternative
open decidable

universes u v

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

def is_none {α : Type u} : option α → bool
| (some _) := ff
| none     := tt

def get {α : Type u} : Π {o : option α}, is_some o → α
| (some x) h := x
| none     h := false.rec _ $ bool.ff_ne_tt h

def rhoare {α : Type u} : bool → α → option α
| tt a := none
| ff a := some a

def lhoare {α : Type u} : α → option α → α
| a none     := a
| _ (some b) := b

infixr `|>`:1 := rhoare
infixr `<|`:1 := lhoare

@[inline] protected def bind {α : Type u} {β : Type v} : option α → (α → option β) → option β
| none     b := none
| (some a) b := b a

protected def map {α β} (f : α → β) (o : option α) : option β :=
option.bind o (some ∘ f)

theorem map_id {α} : (option.map id : option α → option α) = id :=
funext (λo, match o with | none := rfl | some x := rfl end)

instance : monad option :=
{pure := @some, bind := @option.bind, map := @option.map}

protected def orelse {α : Type u} : option α → option α → option α
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

instance : alternative option :=
{ failure := @none,
  orelse  := @option.orelse }

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
