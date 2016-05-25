/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
import init.functor

structure monad [class] (m : Type → Type) extends functor m : Type :=
(return : Π {a:Type}, a → m a)
(bind   : Π {a b: Type}, m a → (a → m b) → m b)

inline definition return {m : Type → Type} [monad m] {A : Type} (a : A) : m A :=
monad.return m a
