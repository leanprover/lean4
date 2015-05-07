/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.function
Author: Leonardo de Moura

General operations on functions.
-/
namespace function

variables {A : Type} {B : Type} {C : Type} {D : Type} {E : Type}

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

definition app [reducible] {B : A → Type} (f : Πx, B x) (x : A) : B x :=
f x

definition curry [reducible] [unfold-f] : (A × B → C) → A → B → C :=
λ f a b, f (a, b)

definition uncurry [reducible] [unfold-c 5] : (A → B → C) → (A × B → C) :=
λ f p, match p with (a, b) := f a b end

theorem curry_uncurry (f : A → B → C) : curry (uncurry f) = f :=
rfl

theorem uncurry_curry (f : A × B → C) : uncurry (curry f) = f :=
funext (λ p, match p with (a, b) := rfl end)

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

lemma right_inv_eq {finv : B → A} {f : A → B} (rinv : f ∘ finv = id) : ∀ x, f (finv x) = x :=
take x, show (f ∘ finv) x = x, by rewrite rinv

definition injective (f : A → B) : Prop := ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂

definition surjective (f : A → B) : Prop := ∀ b, ∃ a, f a = b

definition has_left_inverse (f : A → B) : Prop := ∃ finv : B → A, finv ∘ f = id

definition has_right_inverse (f : A → B) : Prop := ∃ finv : B → A, f ∘ finv = id

lemma injective_of_has_left_inverse {f : A → B} : has_left_inverse f → injective f :=
assume h, take a b, assume faeqfb,
obtain (finv : B → A) (inv : finv ∘ f = id), from h,
calc a = finv (f a) : by rewrite (left_inv_eq inv)
   ... = finv (f b) : faeqfb
   ... = b          : by rewrite (left_inv_eq inv)

lemma surjective_of_has_right_inverse {f : A → B} : has_right_inverse f → surjective f :=
assume h, take b,
obtain (finv : B → A) (inv : f ∘ finv = id), from h,
let  a : A := finv b in
have h : f a = b, from calc
  f a  = (f ∘ finv) b : rfl
   ... = id b         : by rewrite (right_inv_eq inv)
   ... = b            : rfl,
exists.intro a h
end function

-- copy reducible annotations to top-level
export [reduce-hints] [unfold-hints] function
