/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.functor
universe variables u v

class applicative (F : Type u → Type v) extends functor F : Type (max u+1 v):=
(pure : Π {A : Type u}, A → F A)
(seq  : Π {A B : Type u}, F (A → B) → F A → F B)

attribute [inline]
def pure {F : Type u → Type v} [applicative F] {A : Type u} : A → F A :=
applicative.pure F

attribute [inline]
def seq_app {A B : Type u} {F : Type u → Type v} [applicative F] : F (A → B) → F A → F B :=
applicative.seq

infixr ` <*> `:2 := seq_app
