/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.functor

structure applicative [class] (f : Type → Type) extends functor f :=
(pure : Π {A : Type}, A → f A)
(seq  : Π {A B : Type}, f (A → B) → f A → f B)

inline definition pure {f : Type → Type} [applicative f] {A : Type} (a : A) : f A :=
applicative.pure f a

inline definition seq_app {A B : Type} {f : Type → Type} [applicative f] (g : f (A → B)) (a : f A) : f B :=
applicative.seq g a

infixr ` <*> `:2 := seq_app
