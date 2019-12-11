/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Monad
import Init.Data.Option.Basic
universes u v

class HasToBool (α : Type u) :=
(toBool : α → Bool)

export HasToBool (toBool)

instance : HasToBool Bool := ⟨id⟩
instance {α} : HasToBool (Option α) := ⟨Option.toBool⟩

@[macroInline] def bool {β : Type u} {α : Type v} [HasToBool β] (f t : α) (b : β) : α :=
match toBool b with
| true  => t
| false => f

@[macroInline] def orM {m : Type u → Type v} {β : Type u} [Monad m] [HasToBool β] (x y : m β) : m β := do
b ← x;
match toBool b with
| true  => pure b
| false => y

@[macroInline] def andM {m : Type u → Type v} {β : Type u} [Monad m] [HasToBool β] (x y : m β) : m β := do
b ← x;
match toBool b with
| true  => y
| false => pure b

infixl ` <||> `:30 := orM
infixl ` <&&> `:35 := andM

@[macroInline] def notM {m : Type → Type v} [Applicative m] (x : m Bool) : m Bool :=
not <$> x
