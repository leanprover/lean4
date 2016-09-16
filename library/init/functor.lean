/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
set_option new_elaborator true

structure [class] functor (F : Type → Type) : Type :=
(map : Π {A B: Type}, (A → B) → F A → F B)

attribute [inline]
definition fmap {F : Type → Type} [functor F] {A B : Type} : (A → B) → F A → F B :=
functor.map

infixr ` <$> `:100 := fmap
