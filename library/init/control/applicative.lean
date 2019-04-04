/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.functor
open Function
universes u v

class HasPure (f : Type u → Type v) :=
(pure {} {α : Type u} : α → f α)

export HasPure (pure)

class HasSeq (f : Type u → Type v) : Type (max (u+1) v) :=
(seq  : Π {α β : Type u}, f (α → β) → f α → f β)

infixl <*> := HasSeq.seq

class HasSeqLeft (f : Type u → Type v) : Type (max (u+1) v) :=
(seqLeft : Π {α β : Type u}, f α → f β → f α)

infixl <* := HasSeqLeft.seqLeft

class HasSeqRight (f : Type u → Type v) : Type (max (u+1) v) :=
(seqRight : Π {α β : Type u}, f α → f β → f β)

infixr *> := HasSeqRight.seqRight

class Applicative (f : Type u → Type v) extends Functor f, HasPure f, HasSeq f, HasSeqLeft f, HasSeqRight f :=
(map      := λ _ _ x y, pure x <*> y)
(seqLeft  := λ α β a b, const β <$> a <*> b)
(seqRight := λ α β a b, const α id <$> a <*> b)
