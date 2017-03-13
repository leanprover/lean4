/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.category.functor
open function
universes u v

section
set_option auto_param.check_exists false

class applicative (f : Type u → Type v) extends functor f :=
(pure : Π {α : Type u}, α → f α)
(seq  : Π {α β : Type u}, f (α → β) → f α → f β)
(map := λ _ _ x y, seq (pure x) y)
(seq_left : Π {α β : Type u}, f α → f β → f α := λ α β a b, seq (map (const β) a) b)
(seq_right : Π {α β : Type u}, f α → f β → f β := λ α β a b, seq (map (const α id) a) b)
(seq_left_eq : ∀ {α β : Type u} (a : f α) (b : f β), seq_left a b = seq (map (const β) a) b . control_laws_tac)
(seq_right_eq : ∀ {α β : Type u} (a : f α) (b : f β), seq_right a b = seq (map (const α id) a) b . control_laws_tac)
end

section
variables {f : Type u → Type v} [applicative f] {α β : Type u}

@[inline] def pure : α → f α :=
applicative.pure f

@[inline] def seq_app : f (α → β) → f α → f β :=
applicative.seq

/-- Sequence actions, discarding the first value. -/
@[inline] def seq_left : f α → f β → f α :=
applicative.seq_left

/-- Sequence actions, discarding the second value. -/
@[inline] def seq_right : f α → f β → f β :=
applicative.seq_right

infixl ` <*> `:2 := seq_app
infixl ` <* `:2  := seq_left
infixl ` *> `:2  := seq_right
end
