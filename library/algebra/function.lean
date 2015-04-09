/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.function
Author: Leonardo de Moura

General operations on functions.
-/
namespace function

variables {A : Type} {B : Type} {C : Type} {D : Type} {E : Type}

definition compose [reducible] (f : B → C) (g : A → B) : A → C :=
λx, f (g x)

definition compose_right [reducible] (f : B → B → B) (g : A → B) : B → A → B :=
λ b a, f b (g a)

definition compose_left [reducible] (f : B → B → B) (g : A → B) : A → B → B :=
λ a b, f (g a) b

definition id [reducible] (a : A) : A :=
a

definition on_fun [reducible] (f : B → B → C) (g : A → B) : A → A → C :=
λx y, f (g x) (g y)

definition combine [reducible] (f : A → B → C) (op : C → D → E) (g : A → B → D) : A → B → E :=
λx y, op (f x y) (g x y)

definition const [reducible] (B : Type) (a : A) : B → A :=
λx, a

definition dcompose [reducible] {B : A → Type} {C : Π {x : A}, B x → Type}
  (f : Π {x : A} (y : B x), C y) (g : Πx, B x) : Πx, C (g x) :=
λx, f (g x)

definition flip [reducible] {C : A → B → Type} (f : Πx y, C x y) : Πy x, C x y :=
λy x, f x y

definition app [reducible] {B : A → Type} (f : Πx, B x) (x : A) : B x :=
f x

precedence `∘'`:60
precedence `on`:1
precedence `$`:1

infixr  ∘                  := compose
infixr  ∘'                 := dcompose
infixl  on                 := on_fun
infixr  $                  := app
notation f `-[` op `]-` g  := combine f op g

lemma left_inv_eq {finv : B → A} {f : A → B} (linv : finv ∘ f = id) : ∀ x, finv (f x) = x :=
take x, show (finv ∘ f) x = x, by rewrite linv

definition injective (f : A → B) : Prop := ∃ finv : B → A, finv ∘ f = id

lemma injective_def {f : A → B} (h : injective f) : ∀ a b, f a = f b → a = b :=
take a b, assume faeqfb,
obtain (finv : B → A) (inv : finv ∘ f = id), from h,
calc a = finv (f a) : by rewrite (left_inv_eq inv)
   ... = finv (f b) : faeqfb
   ... = b          : by rewrite (left_inv_eq inv)

end function

-- copy reducible annotations to top-level
export [reduce-hints] function
