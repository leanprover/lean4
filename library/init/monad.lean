/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
import init.applicative init.string init.trace
set_option new_elaborator true

structure [class] monad (M : Type → Type) extends functor M : Type :=
(ret  : Π {A : Type}, A → M A)
(bind : Π {A B : Type}, M A → (A → M B) → M B)

attribute [inline]
definition return {M : Type → Type} [monad M] {A : Type} : A → M A :=
monad.ret M

definition {u} fapp {m : Type → Type} [monad m] {A B : Type u} (f : m (A → B)) (a : m A) : m B :=
do g ← f,
   b ← a,
   return (g b)

attribute [inline, instance]
definition monad_is_applicative (m : Type → Type) [monad m] : applicative m :=
applicative.mk (@fmap _ _) (@return _ _) (@fapp _ _)

attribute [inline]
definition monad.and_then {A B : Type} {m : Type → Type} [monad m] (a : m A) (b : m B) : m B :=
do a, b

infixl ` >>= `:2 := monad.bind
infixl ` >> `:2  := monad.and_then
