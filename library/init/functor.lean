/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
universe variables u v

class functor (f : Type u → Type v) : Type (max u+1 v) :=
(map : Π {a b : Type u}, (a → b) → f a → f b)

@[inline] def fmap {f : Type u → Type v} [functor f] {a b : Type u} : (a → b) → f a → f b :=
functor.map

infixr ` <$> `:100 := fmap
