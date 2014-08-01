-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
namespace function

section
  parameters {A : Type} {B : Type} {C : Type} {D : Type} {E : Type}

  abbreviation compose (f : B → C) (g : A → B) : A → C :=
  λx, f (g x)

  abbreviation id (a : A) : A :=
  a

  abbreviation on_fun (f : B → B → C) (g : A → B) : A → A → C :=
  λx y, f (g x) (g y)

  abbreviation combine (f : A → B → C) (op : C → D → E) (g : A → B → D) : A → B → E :=
  λx y, op (f x y) (g x y)
end

abbreviation const {A : Type} (B : Type) (a : A) : B → A :=
λx, a

abbreviation dcompose {A : Type} {B : A → Type} {C : Π {x : A}, B x → Type} (f : Π {x : A} (y : B x), C y) (g : Πx, B x) : Πx, C (g x) :=
λx, f (g x)

abbreviation flip {A : Type} {B : Type} {C : A → B → Type} (f : Πx y, C x y) : Πy x, C x y :=
λy x, f x y

abbreviation app {A : Type} {B : A → Type} (f : Πx, B x) (x : A) : B x :=
f x

-- Yet another trick to anotate an expression with a type
abbreviation is_typeof (A : Type) (a : A) : A :=
a

precedence `∘`:60
precedence `∘'`:60
precedence `on`:1
precedence `$`:1
precedence `-[`:1
precedence `]-`:1
precedence `⟨`:1

infixr  ∘                  := compose
infixr  ∘'                 := dcompose
infixl  on                 := on_fun
notation `typeof` t `:` T  := is_typeof T t
infixr  $                  := app
notation f `-[` op `]-` g  := combine f op g
-- Trick for using any binary function as infix operator
notation a `⟨` f `⟩` b     :=  f a b

end
