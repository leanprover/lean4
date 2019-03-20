/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.functor
open function
universes u v

class hasPure (f : Type u → Type v) :=
(pure {} {α : Type u} : α → f α)

export hasPure (pure)

class hasSeq (f : Type u → Type v) : Type (max (u+1) v) :=
(seq  : Π {α β : Type u}, f (α → β) → f α → f β)

infixl ` <*> `:60 := hasSeq.seq

class hasSeqLeft (f : Type u → Type v) : Type (max (u+1) v) :=
(seqLeft : Π {α β : Type u}, f α → f β → f α)

infixl ` <* `:60  := hasSeqLeft.seqLeft

class hasSeqRight (f : Type u → Type v) : Type (max (u+1) v) :=
(seqRight : Π {α β : Type u}, f α → f β → f β)

infixl ` *> `:60  := hasSeqRight.seqRight

class applicative (f : Type u → Type v) extends functor f, hasPure f, hasSeq f, hasSeqLeft f, hasSeqRight f :=
(map       := λ _ _ x y, pure x <*> y)
(seqLeft  := λ α β a b, const β <$> a <*> b)
(seqRight := λ α β a b, const α id <$> a <*> b)
