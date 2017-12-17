/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.option.basic
import init.meta.tactic
import init.category.lawful

universes u v

instance : is_lawful_monad option :=
{ id_map := λ α x, option.rec rfl (λ x, rfl) x,
  pure_bind := λ α β x f, rfl,
  bind_assoc := λ α β γ x f g, option.rec rfl (λ x, rfl) x }

lemma option.eq_of_eq_some {α : Type u} : Π {x y : option α}, (∀z, x = some z ↔ y = some z) → x = y
| none     none     h := rfl
| none     (some z) h := option.no_confusion ((h z).2 rfl)
| (some z) none     h := option.no_confusion ((h z).1 rfl)
| (some z) (some w) h := option.no_confusion ((h w).2 rfl) (congr_arg some)

lemma option.eq_some_of_is_some {α : Type u} : Π {o : option α} (h : option.is_some o), o = some (option.get h)
| (some x) h := rfl

lemma option.eq_none_of_is_none {α : Type u} : Π {o : option α}, o.is_none → o = none
| none h := rfl
