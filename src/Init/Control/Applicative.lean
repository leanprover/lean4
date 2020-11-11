/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Control.Functor
open Function
universes u v

@[macroInline]
def when {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
  if c then t else pure ()

@[macroInline]
def «unless» {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (e : m Unit) : m Unit :=
  if c then pure () else e
