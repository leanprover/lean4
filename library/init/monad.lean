/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
import init.applicative init.string init.trace
universe variables u v

class monad (m : Type u → Type v) extends functor m : Type (max u+1 v) :=
(ret  : Π {a : Type u}, a → m a)
(bind : Π {a b : Type u}, m a → (a → m b) → m b)

@[inline] def return {m : Type u → Type v} [monad m] {a : Type u} : a → m a :=
monad.ret m

def fapp {m : Type u → Type v} [monad m] {a b : Type u} (f : m (a → b)) (a : m a) : m b :=
do g ← f,
   b ← a,
   return (g b)

@[inline] instance monad_is_applicative (m : Type u → Type v) [monad m] : applicative m :=
⟨@fmap _ _, @return _ _, @fapp _ _⟩

@[inline] def monad.and_then {a b : Type u} {m : Type u → Type v} [monad m] (x : m a) (y : m b) : m b :=
do x, y

infixl ` >>= `:2 := monad.bind
infixl ` >> `:2  := monad.and_then
