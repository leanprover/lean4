/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Monad
import Init.Data.Option.Basic
universes u v

class ToBool (α : Type u) :=
  (toBool : α → Bool)

export ToBool (toBool)

instance : ToBool Bool := ⟨id⟩
instance {α} : ToBool (Option α) := ⟨Option.toBool⟩

@[macroInline] def bool {β : Type u} {α : Type v} [ToBool β] (f t : α) (b : β) : α :=
  match toBool b with
  | true  => t
  | false => f

@[macroInline] def orM {m : Type u → Type v} {β : Type u} [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true  => pure b
  | false => y

@[macroInline] def andM {m : Type u → Type v} {β : Type u} [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true  => y
  | false => pure b

@[macroInline] def notM {m : Type → Type v} [Applicative m] (x : m Bool) : m Bool :=
  not <$> x
