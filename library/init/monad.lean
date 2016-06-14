/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
import init.functor init.string init.trace

structure monad [class] (m : Type → Type) extends functor m : Type :=
(ret  : Π {a:Type}, a → m a)
(bind : Π {a b: Type}, m a → (a → m b) → m b)

inline definition return {m : Type → Type} [monad m] {A : Type} (a : A) : m A :=
monad.ret m a

inline definition fapp {A B : Type} {m : Type → Type} [monad m] (f : m (A → B)) (a : m A) : m B :=
do g ← f,
   b ← a,
   return (g b)

infixr ` <*> `:100 := fapp
infixl ` >>= `:100 := monad.bind
