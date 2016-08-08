/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
import init.applicative init.string init.trace

structure monad [class] (m : Type → Type) extends functor m : Type :=
(ret  : Π {a:Type}, a → m a)
(bind : Π {a b: Type}, m a → (a → m b) → m b)

definition return [inline] {m : Type → Type} [monad m] {A : Type} (a : A) : m A :=
monad.ret m a

definition fapp {m : Type → Type} [monad m] {A B : Type} (f : m (A → B)) (a : m A) : m B :=
do g ← f,
   b ← a,
   return (g b)

definition monad_is_applicative [inline] [instance] (m : Type → Type) [monad m] : applicative m :=
applicative.mk (@monad.map _ _) (@monad.ret _ _) (@fapp _ _)

definition monad.and_then [inline] {A B : Type} {m : Type → Type} [monad m] (a : m A) (b : m B) : m B :=
do a, b

infixl ` >>= `:2 := monad.bind
infixl ` >> `:2  := monad.and_then
