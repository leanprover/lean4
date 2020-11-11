/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import Init.Control.Applicative
import Init.Coe
universes u v w

open Function

@[inline] def mcomp {α : Type u} {β δ : Type v} {m : Type v → Type w} [Bind m] (f : α → m β) (g : β → m δ) : α → m δ :=
  fun a => f a >>= g

def joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
  bind a id

@[macroInline]
def condM {m : Type → Type u} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool; cond b tm fm

@[macroInline]
def whenM {m : Type → Type u} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
  condM c t (pure ())

@[macroInline]
def unlessM {m : Type → Type u} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
  condM c (pure ()) t

@[inline] def coeM {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] (x : m α) : m β := do
  let a ← x
  pure $ coe a
