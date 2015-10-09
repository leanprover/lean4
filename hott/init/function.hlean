/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

General operations on functions.
-/

prelude
import init.reserved_notation .types

open prod

namespace function

variables {A B C D E : Type}

definition compose [reducible] [unfold_full] (f : B → C) (g : A → B) : A → C :=
λx, f (g x)

definition compose_right [reducible] [unfold_full] (f : B → B → B) (g : A → B) : B → A → B :=
λ b a, f b (g a)

definition compose_left [reducible] [unfold_full] (f : B → B → B) (g : A → B) : A → B → B :=
λ a b, f (g a) b

definition id [reducible] [unfold_full] (a : A) : A :=
a

definition on_fun [reducible] [unfold_full] (f : B → B → C) (g : A → B) : A → A → C :=
λx y, f (g x) (g y)

definition combine [reducible] [unfold_full] (f : A → B → C) (op : C → D → E) (g : A → B → D)
  : A → B → E :=
λx y, op (f x y) (g x y)

definition const [reducible] [unfold_full] (B : Type) (a : A) : B → A :=
λx, a

definition dcompose [reducible] [unfold_full] {B : A → Type} {C : Π {x : A}, B x → Type}
  (f : Π {x : A} (y : B x), C y) (g : Πx, B x) : Πx, C (g x) :=
λx, f (g x)

definition flip [reducible] [unfold_full] {C : A → B → Type} (f : Πx y, C x y) : Πy x, C x y :=
λy x, f x y

definition app [reducible] [unfold_full] {B : A → Type} (f : Πx, B x) (x : A) : B x :=
f x

definition curry [reducible] [unfold_full] : (A × B → C) → A → B → C :=
λ f a b, f (a, b)

definition uncurry [reducible] [unfold 5] : (A → B → C) → (A × B → C) :=
λ f p, match p with (a, b) := f a b end


infixr  ` ∘ `            := compose
infixr  ` ∘' `:60        := dcompose
infixl  ` on `:1         := on_fun
infixr  ` $ `:1          := app
notation f ` -[` op `]- ` g  := combine f op g

end function

-- copy reducible annotations to top-level
export [reduce_hints] [unfold_hints] function
