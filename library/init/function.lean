/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang

General operations on functions.
-/
prelude
import init.prod init.funext init.logic

namespace function

variables {A : Type} {B : Type} {C : Type} {D : Type} {E : Type}

definition compose [reducible] [unfold-full] (f : B → C) (g : A → B) : A → C :=
λx, f (g x)

definition compose_right [reducible] [unfold-full] (f : B → B → B) (g : A → B) : B → A → B :=
λ b a, f b (g a)

definition compose_left [reducible] [unfold-full] (f : B → B → B) (g : A → B) : A → B → B :=
λ a b, f (g a) b

definition id [reducible] [unfold-full] (a : A) : A :=
a

definition on_fun [reducible] [unfold-full] (f : B → B → C) (g : A → B) : A → A → C :=
λx y, f (g x) (g y)

definition combine [reducible] [unfold-full] (f : A → B → C) (op : C → D → E) (g : A → B → D)
  : A → B → E :=
λx y, op (f x y) (g x y)

definition const [reducible] [unfold-full] (B : Type) (a : A) : B → A :=
λx, a

definition dcompose [reducible] [unfold-full] {B : A → Type} {C : Π {x : A}, B x → Type}
  (f : Π {x : A} (y : B x), C y) (g : Πx, B x) : Πx, C (g x) :=
λx, f (g x)

definition swap [reducible] [unfold-full] {C : A → B → Type} (f : Πx y, C x y) : Πy x, C x y :=
λy x, f x y

definition app [reducible] {B : A → Type} (f : Πx, B x) (x : A) : B x :=
f x

definition curry [reducible] [unfold-full] : (A × B → C) → A → B → C :=
λ f a b, f (a, b)

definition uncurry [reducible] [unfold 5] : (A → B → C) → (A × B → C) :=
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

lemma left_id (f : A → B) : id ∘ f = f := rfl

lemma right_id (f : A → B) : f ∘ id = f := rfl

theorem compose.assoc (f : C → D) (g : B → C) (h : A → B) : (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

theorem compose.left_id (f : A → B) : id ∘ f = f := rfl

theorem compose.right_id (f : A → B) : f ∘ id = f := rfl

theorem compose_const_right (f : B → C) (b : B) : f ∘ (const A b) = const A (f b) := rfl

definition injective [reducible] (f : A → B) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

theorem injective_compose {g : B → C} {f : A → B} (Hg : injective g) (Hf : injective f) :
  injective (g ∘ f) :=
take a₁ a₂, assume Heq, Hf (Hg Heq)

definition surjective [reducible] (f : A → B) : Prop := ∀ b, ∃ a, f a = b

theorem surjective_compose {g : B → C} {f : A → B} (Hg : surjective g) (Hf : surjective f) :
  surjective (g ∘ f) :=
take c,
  obtain b (Hb : g b = c), from Hg c,
  obtain a (Ha : f a = b), from Hf b,
  exists.intro a (eq.trans (congr_arg g Ha) Hb)

definition bijective (f : A → B) := injective f ∧ surjective f

theorem bijective_compose {g : B → C} {f : A → B} (Hg : bijective g) (Hf : bijective f) :
  bijective (g ∘ f) :=
obtain Hginj Hgsurj, from Hg,
obtain Hfinj Hfsurj, from Hf,
and.intro (injective_compose Hginj Hfinj) (surjective_compose Hgsurj Hfsurj)

-- g is a left inverse to f
definition left_inverse (g : B → A) (f : A → B) : Prop := ∀x, g (f x) = x

definition id_of_left_inverse {g : B → A} {f : A → B} : left_inverse g f → g ∘ f = id :=
assume h, funext h

definition has_left_inverse (f : A → B) : Prop := ∃ finv : B → A, left_inverse finv f

-- g is a right inverse to f
definition right_inverse (g : B → A) (f : A → B) : Prop := left_inverse f g

definition id_of_righ_inverse {g : B → A} {f : A → B} : right_inverse g f → f ∘ g = id :=
assume h, funext h

definition has_right_inverse (f : A → B) : Prop := ∃ finv : B → A, right_inverse finv f

theorem injective_of_left_inverse {g : B → A} {f : A → B} : left_inverse g f → injective f :=
assume h, take a b, assume faeqfb,
calc a = g (f a) : by rewrite h
   ... = g (f b) : faeqfb
   ... = b       : by rewrite h

theorem injective_of_has_left_inverse {f : A → B} : has_left_inverse f → injective f :=
assume h, obtain (finv : B → A) (inv : left_inverse finv f), from h,
injective_of_left_inverse inv

theorem right_inverse_of_injective_of_left_inverse {f : A → B} {g : B → A}
    (injf : injective f) (lfg : left_inverse f g) :
  right_inverse f g :=
take x,
have H : f (g (f x)) = f x, from lfg (f x),
injf H

theorem surjective_of_has_right_inverse {f : A → B} : has_right_inverse f → surjective f :=
assume h, take b,
obtain (finv : B → A) (inv : right_inverse finv f), from h,
let  a : A := finv b in
have h : f a = b, from calc
  f a  = (f ∘ finv) b : rfl
   ... = id b         : by rewrite inv
   ... = b            : rfl,
exists.intro a h

theorem left_inverse_of_surjective_of_right_inverse {f : A → B} {g : B → A}
    (surjf : surjective f) (rfg : right_inverse f g) :
  left_inverse f g :=
take y,
obtain x (Hx : f x = y), from surjf y,
calc
  f (g y) = f (g (f x)) : Hx
      ... = f x         : rfg
      ... = y           : Hx

theorem injective_id : injective (@id A) := take a₁ a₂ H, H

theorem surjective_id : surjective (@id A) := take a, exists.intro a rfl

theorem bijective_id : bijective (@id A) := and.intro injective_id surjective_id

end function

-- copy reducible annotations to top-level
export [reduce-hints] [unfold-hints] function
