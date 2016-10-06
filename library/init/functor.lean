/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
universe variables u v

class functor (F : Type u → Type v) : Type (max u+1 v) :=
(map : Π {A B : Type u}, (A → B) → F A → F B)

@[inline] def fmap {F : Type u → Type v} [functor F] {A B : Type u} : (A → B) → F A → F B :=
functor.map

infixr ` <$> `:100 := fmap
