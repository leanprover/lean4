/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.function
Author: Leonardo de Moura

General operations on functions.
-/

prelude
import init.reserved_notation .types

open prod

namespace function

variables {A B C D E : Type}

definition compose [reducible] [unfold-f] (f : B → C) (g : A → B) : A → C :=
λx, f (g x)

definition compose_right [reducible] [unfold-f] (f : B → B → B) (g : A → B) : B → A → B :=
λ b a, f b (g a)

definition compose_left [reducible] [unfold-f] (f : B → B → B) (g : A → B) : A → B → B :=
λ a b, f (g a) b

definition id [reducible] [unfold-f] (a : A) : A :=
a

definition on_fun [reducible] [unfold-f] (f : B → B → C) (g : A → B) : A → A → C :=
λx y, f (g x) (g y)

definition combine [reducible] [unfold-f] (f : A → B → C) (op : C → D → E) (g : A → B → D)
  : A → B → E :=
λx y, op (f x y) (g x y)

definition const [reducible] [unfold-f] (B : Type) (a : A) : B → A :=
λx, a

definition dcompose [reducible] [unfold-f] {B : A → Type} {C : Π {x : A}, B x → Type}
  (f : Π {x : A} (y : B x), C y) (g : Πx, B x) : Πx, C (g x) :=
λx, f (g x)

definition flip [reducible] [unfold-f] {C : A → B → Type} (f : Πx y, C x y) : Πy x, C x y :=
λy x, f x y

definition app [reducible] [unfold-f] {B : A → Type} (f : Πx, B x) (x : A) : B x :=
f x

definition curry [reducible] [unfold-f] : (A × B → C) → A → B → C :=
λ f a b, f (a, b)

definition uncurry [reducible] [unfold-c 5] : (A → B → C) → (A × B → C) :=
λ f p, match p with (a, b) := f a b end

precedence `∘'`:60
precedence `on`:1
precedence `$`:1


infixr  ∘                  := compose
infixr  ∘'                 := dcompose
infixl  on                 := on_fun
infixr  $                  := app
notation f `-[` op `]-` g  := combine f op g

end function

-- copy reducible annotations to top-level
export [reduce-hints] [unfold-hints] function
