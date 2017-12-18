/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.category.functor
open function
universes u v

class has_pure (f : Type u → Type v) :=
(pure {} {α : Type u} : α → f α)

export has_pure (pure)

class has_seq (f : Type u → Type v) : Type (max (u+1) v) :=
(seq  : Π {α β : Type u}, f (α → β) → f α → f β)

infixl ` <*> `:60 := has_seq.seq

class has_seq_left (f : Type u → Type v) : Type (max (u+1) v) :=
(seq_left : Π {α β : Type u}, f α → f β → f α)

infixl ` <* `:60  := has_seq_left.seq_left

class has_seq_right (f : Type u → Type v) : Type (max (u+1) v) :=
(seq_right : Π {α β : Type u}, f α → f β → f β)

infixl ` *> `:60  := has_seq_right.seq_right

section
set_option auto_param.check_exists false

class applicative (f : Type u → Type v) extends functor f, has_pure f, has_seq f, has_seq_left f, has_seq_right f :=
(map       := λ _ _ x y, pure x <*> y)
(seq_left  := λ α β a b, const β <$> a <*> b)
(seq_right := λ α β a b, const α id <$> a <*> b)
(seq_left_eq  : ∀ {α β : Type u} (a : f α) (b : f β), a <* b = const β <$> a <*> b . control_laws_tac)
(seq_right_eq : ∀ {α β : Type u} (a : f α) (b : f β), a *> b = const α id <$> a <*> b . control_laws_tac)
-- applicative laws
(pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x) -- . control_laws_tac)
(map_pure        : ∀ {α β : Type u} (g : α → β) (x : α), g <$> pure x = pure (g x))
(seq_pure        : ∀ {α β : Type u} (g : f (α → β)) (x : α), g <*> pure x = (λ g : α → β, g x) <$> g)
(seq_assoc       : ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)), h <*> (g <*> x) = (@comp α β γ <$> h) <*> g <*> x)
-- defaulted functor law
(map_comp :=
 λ α β γ g h x, calc
  (h ∘ g) <$> x = pure (h ∘ g) <*> x                        : eq.symm $ pure_seq_eq_map _ _
            ... = (comp h <$> pure g) <*> x                 : eq.rec rfl $ map_pure (comp h) g
            ... = pure (@comp α β γ h) <*> pure g <*> x     : eq.rec rfl $ eq.symm $ pure_seq_eq_map (comp h) (pure g)
            ... = (@comp α β γ <$> pure h) <*> pure g <*> x : eq.rec rfl $ map_pure (@comp α β γ) h
            ... = pure h <*> (pure g <*> x)                 : eq.symm $ seq_assoc _ _ _
            ... = h <$> (pure g <*> x)                      : pure_seq_eq_map _ _
            ... = h <$> g <$> x                             : congr_arg _ $ pure_seq_eq_map _ _)
end

-- applicative "law" derivable from other laws
theorem applicative.pure_id_seq {α β : Type u} {f : Type u → Type v} [applicative f] (x : f α) : pure id <*> x = x :=
eq.trans (applicative.pure_seq_eq_map _ _) (functor.id_map _)
