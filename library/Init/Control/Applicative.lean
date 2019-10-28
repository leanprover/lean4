/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Control.Functor
open Function
universes u v

class HasPure (f : Type u → Type v) :=
(pure {} {α : Type u} : α → f α)

export HasPure (pure)

class HasSeq (f : Type u → Type v) : Type (max (u+1) v) :=
(seq  : ∀ {α β : Type u}, f (α → β) → f α → f β)

infixl <*> := HasSeq.seq

class HasSeqLeft (f : Type u → Type v) : Type (max (u+1) v) :=
(seqLeft : ∀ {α β : Type u}, f α → f β → f α)

infixl <* := HasSeqLeft.seqLeft

class HasSeqRight (f : Type u → Type v) : Type (max (u+1) v) :=
(seqRight : ∀ {α β : Type u}, f α → f β → f β)

infixr *> := HasSeqRight.seqRight

class Applicative (f : Type u → Type v) extends Functor f, HasPure f, HasSeq f, HasSeqLeft f, HasSeqRight f :=
(map      := fun _ _ x y => pure x <*> y)
(seqLeft  := fun α β a b => const β <$> a <*> b)
(seqRight := fun α β a b => const α id <$> a <*> b)

@[macroInline]
def when {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
if c then t else pure ()

@[macroInline]
def unless {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (e : m Unit) : m Unit :=
if c then pure () else e
