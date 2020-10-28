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
  (pure {α : Type u} : α → f α)

export HasPure (pure)

class HasSeq (f : Type u → Type v) : Type (max (u+1) v) :=
  (seq  : {α β : Type u} → f (α → β) → f α → f β)

class HasSeqLeft (f : Type u → Type v) : Type (max (u+1) v) :=
  (seqLeft : {α : Type u} → f α → f PUnit → f α)

class HasSeqRight (f : Type u → Type v) : Type (max (u+1) v) :=
  (seqRight : {β : Type u} → f PUnit → f β → f β)

class Pure (f : Type u → Type v) :=
  (pure {α : Type u} : α → f α)

class Seq (f : Type u → Type v) : Type (max (u+1) v) :=
  (seq  : {α β : Type u} → f (α → β) → f α → f β)

class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) :=
  (seqLeft : {α : Type u} → f α → f PUnit → f α)

class SeqRight (f : Type u → Type v) : Type (max (u+1) v) :=
  (seqRight : {β : Type u} → f PUnit → f β → f β)

class Applicative (f : Type u → Type v) extends Functor f, HasPure f, HasSeq f, HasSeqLeft f, HasSeqRight f :=
  (map      := fun x y => pure x <*> y)
  (seqLeft  := fun a b => const _ <$> a <*> b)
  (seqRight := fun a b => const _ id <$> a <*> b)

@[macroInline]
def when {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
  if c then t else pure ()

@[macroInline]
def «unless» {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (e : m Unit) : m Unit :=
  if c then pure () else e
