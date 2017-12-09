/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.category.functor
open function
universes u v

class has_pure (f : Type u → Type v) :=
(pure {} {α : Type u} : α → f α)

export has_pure (pure)

class has_seq (f : Type u → Type v) : Type (max (u+1) v) :=
(seq  : Π {α β : Type u}, f (α → β) → f α → f β)

infixl ` <*> `:60 := has_seq.seq

class has_seq_left (f : Type u → Type v) : Type (max (u+1) v) :=
(seq_left : Π {α β : Type u}, f α → f β → f α)

infixl ` <* `:60  := has_seq_left.seq_left

class has_seq_right (f : Type u → Type v) : Type (max (u+1) v) :=
(seq_right : Π {α β : Type u}, f α → f β → f β)

infixl ` *> `:60  := has_seq_right.seq_right

class applicative (f : Type u → Type v) extends functor f, has_pure f, has_seq f, has_seq_left f, has_seq_right f :=
(map       := λ _ _ x y, pure x <*> y)
(seq_left  := λ α β a b, const β <$> a <*> b)
(seq_right := λ α β a b, const α id <$> a <*> b)
