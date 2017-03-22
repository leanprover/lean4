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
(infixr ` <$> `:100 := map)
(infixl ` <*> `:60 := seq)
(map := λ _ _ x y, pure x <*> y)
-- ` <* `
(seq_left : Π {α β : Type u}, f α → f β → f α := λ α β a b, seq (map (const β) a) b)
(seq_left_eq : ∀ {α β : Type u} (a : f α) (b : f β), seq_left a b = seq (map (const β) a) b . control_laws_tac)
-- ` *> `
(seq_right : Π {α β : Type u}, f α → f β → f β := λ α β a b, seq (map (const α id) a) b)
(seq_right_eq : ∀ {α β : Type u} (a : f α) (b : f β), seq_right a b = seq (map (const α id) a) b . control_laws_tac)
-- applicative laws
(pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x) -- . control_laws_tac)
(map_pure : ∀ {α β : Type u} (g : α → β) (x : α), g <$> pure x = pure (g x))
(seq_pure : ∀ {α β : Type u} (g : f (α → β)) (x : α),
  g <*> pure x = (λ g : α → β, g x) <$> g)
(seq_assoc : ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)),
  h <*> (g <*> x) = (@comp α β γ <$> h) <*> g <*> x)
-- defaulted functor law
(map_comp := λ α β γ g h x, calc
  (h ∘ g) <$> x = pure (h ∘ g) <*> x                        : eq.symm $ pure_seq_eq_map _ _
            ... = (comp h <$> pure g) <*> x                 : eq.rec rfl $ map_pure (comp h) g
            ... = pure (@comp α β γ h) <*> pure g <*> x     : eq.rec rfl $ eq.symm $ pure_seq_eq_map (comp h) (pure g)
            ... = (@comp α β γ <$> pure h) <*> pure g <*> x : eq.rec rfl $ map_pure (@comp α β γ) h
            ... = pure h <*> (pure g <*> x)                 : eq.symm $ seq_assoc _ _ _
            ... = h <$> (pure g <*> x)                      : pure_seq_eq_map _ _
            ... = h <$> g <$> x                             : congr_arg _ $ pure_seq_eq_map _ _)
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

infixl ` <*> `:60 := seq_app
infixl ` <* `:60  := seq_left
infixl ` *> `:60  := seq_right

end

-- applicative "law" derivable from other laws
theorem applicative.pure_id_seq {α β : Type u} {f : Type u → Type v} [applicative f] (x : f α) : pure id <*> x = x :=
eq.trans (applicative.pure_seq_eq_map _ _) (functor.id_map _)
