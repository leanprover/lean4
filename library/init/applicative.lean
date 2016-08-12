/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.functor

set_option pp.all true

structure applicative.{u₁ u₂} [class] (f : Type.{u₁} → Type.{u₂}) extends functor f : Type.{max u₁+1 u₂} :=
(pure : Π {A : Type.{u₁}}, A → f A)
(seq  : Π {A B : Type.{u₁}}, f (A → B) → f A → f B)

attribute [inline]
definition pure {f : Type → Type} [applicative f] {A : Type} (a : A) : f A :=
applicative.pure f a

attribute [inline]
definition seq_app {A B : Type} {f : Type → Type} [applicative f] (g : f (A → B)) (a : f A) : f B :=
applicative.seq g a

infixr ` <*> `:2 := seq_app
