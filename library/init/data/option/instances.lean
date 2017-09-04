/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.option.basic
import init.meta.tactic

universes u v

@[inline] def option.bind {α : Type u} {β : Type v} : option α → (α → option β) → option β
| none     b := none
| (some a) b := b a

def option.map {α β} (f : α → β) (o : option α) : option β :=
option.bind o (some ∘ f)

@[simp] theorem option.map_id {α} : (option.map id : option α → option α) = id :=
funext (λo, match o with | none := rfl | some x := rfl end)

instance : monad option :=
{pure := @some, bind := @option.bind, map := @option.map,
 id_map := λ α x, option.rec rfl (λ x, rfl) x,
 pure_bind := λ α β x f, rfl,
 bind_assoc := λ α β γ x f g, option.rec rfl (λ x, rfl) x}

def option.orelse {α : Type u} : option α → option α → option α
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

instance : alternative option :=
{ option.monad with
  failure := @none,
  orelse  := @option.orelse }

lemma option.eq_of_eq_some {α : Type u} : Π {x y : option α}, (∀z, x = some z ↔ y = some z) → x = y
| none     none     h := rfl
| none     (some z) h := option.no_confusion ((h z).2 rfl)
| (some z) none     h := option.no_confusion ((h z).1 rfl)
| (some z) (some w) h := option.no_confusion ((h w).2 rfl) (congr_arg some)

lemma option.eq_some_of_is_some {α : Type u} : Π {o : option α} (h : option.is_some o), o = some (option.get h)
| (some x) h := rfl

lemma option.eq_none_of_is_none {α : Type u} : Π {o : option α}, o.is_none → o = none
| none h := rfl
