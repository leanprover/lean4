/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.category.functor
import init.function
open function
universes u v

class applicative (f : Type u → Type v) extends functor f : Type (max u+1 v):=
(pure : Π {a : Type u}, a → f a)
(seq  : Π {a b : Type u}, f (a → b) → f a → f b)

section
variables {a b : Type u} {f : Type u → Type v} [applicative f]

@[inline] def pure : a → f a :=
applicative.pure f

@[inline] def seq_app : f (a → b) → f a → f b :=
applicative.seq

infixl ` <*> `:2 := seq_app

/-- Sequence actions, discarding the first value. -/
def seq_left (x : f a) (y : f b) : f a :=
pure (λ x y, x) <*> x <*> y

/-- Sequence actions, discarding the second value. -/
def seq_right (x : f a) (y : f b) : f b :=
pure (λ x y, y) <*> x <*> y

infixl ` <* `:2 := seq_left
infixl ` *> `:2 := seq_right

end
