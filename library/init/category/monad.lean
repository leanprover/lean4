/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
import init.category.applicative
universes u v

class pre_monad (m : Type u → Type v) :=
(bind : Π {a b : Type u}, m a → (a → m b) → m b)

@[inline] def bind {m : Type u → Type v} [pre_monad m] {a b : Type u} : m a → (a → m b) → m b :=
pre_monad.bind

@[inline] def pre_monad.and_then {a b : Type u} {m : Type u → Type v} [pre_monad m] (x : m a) (y : m b) : m b :=
do x, y

class monad (m : Type u → Type v) extends functor m, pre_monad m : Type (max u+1 v) :=
(ret  : Π {a : Type u}, a → m a)

@[inline] def return {m : Type u → Type v} [monad m] {a : Type u} : a → m a :=
monad.ret m

def fapp {m : Type u → Type v} [monad m] {a b : Type u} (f : m (a → b)) (a : m a) : m b :=
do g ← f,
   b ← a,
   return (g b)

@[inline] instance monad_is_applicative (m : Type u → Type v) [monad m] : applicative m :=
⟨@fmap _ _, @return _ _, @fapp _ _⟩

infixl ` >>= `:2 := bind
infixl ` >> `:2  := pre_monad.and_then

/- Identical to pre_monad.and_then, but it is not inlined. -/
def pre_monad.seq {a b : Type u} {m : Type u → Type v} [pre_monad m] (x : m a) (y : m b) : m b :=
do x, y
