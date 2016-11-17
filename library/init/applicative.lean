/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.functor
universe variables u v

class applicative (f : Type u → Type v) extends functor f : Type (max u+1 v):=
(pure : Π {a : Type u}, a → f a)
(seq  : Π {a b : Type u}, f (a → b) → f a → f b)

@[inline] def pure {f : Type u → Type v} [applicative f] {a : Type u} : a → f a :=
applicative.pure f

@[inline] def seq_app {a b : Type u} {f : Type u → Type v} [applicative f] : f (a → b) → f a → f b :=
applicative.seq

infixr ` <*> `:2 := seq_app
