/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
import init.applicative init.string init.trace
universe variables u v

class monad (M : Type u → Type v) extends functor M : Type (max u+1 v) :=
(ret  : Π {A : Type u}, A → M A)
(bind : Π {A B : Type u}, M A → (A → M B) → M B)

@[inline] def return {M : Type u → Type v} [monad M] {A : Type u} : A → M A :=
monad.ret M

def fapp {M : Type u → Type v} [monad M] {A B : Type u} (f : M (A → B)) (a : M A) : M B :=
do g ← f,
   b ← a,
   return (g b)

@[inline] instance monad_is_applicative (M : Type u → Type v) [monad M] : applicative M :=
⟨@fmap _ _, @return _ _, @fapp _ _⟩

@[inline] def monad.and_then {A B : Type u} {M : Type u → Type v} [monad M] (a : M A) (b : M B) : M B :=
do a, b

infixl ` >>= `:2 := monad.bind
infixl ` >> `:2  := monad.and_then
