/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.functor
set_option new_elaborator true

structure [class] {u₁ u₂} applicative (F : Type u₁ → Type u₂) extends functor F : Type (max u₁+1 u₂) :=
(pure : Π {A : Type u₁}, A → F A)
(seq  : Π {A B : Type u₁}, F (A → B) → F A → F B)

attribute [inline]
definition pure {F : Type → Type} [applicative F] ⦃A : Type⦄ : A → F A :=
applicative.pure F

attribute [inline]
definition {u} seq_app {A B : Type u} {F : Type → Type} [applicative F] : F (A → B) → F A →  F B :=
applicative.seq

infixr ` <*> `:2 := seq_app
