/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import init.category.applicative
universes u v

open function

class has_bind (m : Type u → Type v) :=
(bind : Π {α β : Type u}, m α → (α → m β) → m β)

@[inline] def bind {m : Type u → Type v} [has_bind m] {α β : Type u} : m α → (α → m β) → m β :=
has_bind.bind

@[inline] def has_bind.and_then {α β : Type u} {m : Type u → Type v} [has_bind m] (x : m α) (y : m β) : m β :=
do x, y

infixl ` >>= `:55 := bind
infixl ` >> `:55  := has_bind.and_then

section
set_option auto_param.check_exists false

class monad (m : Type u → Type v) extends applicative m, has_bind m : Type (max u+1 v) :=
(infixr ` <$> `:100 := map)
(infixl ` <*> `:60 := seq)
(infixl ` >>= `:55 := bind)
(map := λ α β f x, x >>= pure ∘ f)
(seq := λ α β f x, f >>= (<$> x))
(bind_pure_comp_eq_map : ∀ {α β : Type u} (f : α → β) (x : m α), x >>= pure ∘ f = f <$> x  . control_laws_tac)
(bind_map_eq_seq : ∀ {α β : Type u} (f : m (α → β)) (x : m α), f >>= (<$> x) = f <*> x  . control_laws_tac)
-- monad laws
(pure_bind : ∀ {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x)
(bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),
  x >>= f >>= g = x >>= λ x, f x >>= g)
-- all applicative laws are derivable from the monad laws + id_map
(pure_seq_eq_map := λ α β g x, eq.trans (eq.symm $ bind_map_eq_seq _ _) (pure_bind _ _))
(map_pure := λ α β g x, eq.trans (eq.symm $ bind_pure_comp_eq_map _ _) (pure_bind _ _))
(seq_pure := λ α β g x, calc
  g <*> pure x = g >>= (<$> pure x)            : eq.symm $ bind_map_eq_seq _ _
           ... = g >>= λ g : α → β, pure (g x) : congr_arg _ $ funext $ λ g, map_pure _ _
           ... = (λ g : α → β, g x) <$> g      : bind_pure_comp_eq_map _ _)
(seq_assoc := λ α β γ x g h, calc
  h <*> (g <*> x)
      = h >>= (<$> g <*> x) : eq.symm $ bind_map_eq_seq _ _
  ... = h >>= λ h, pure (@comp α β γ h) >>= (<$> g) >>= (<$> x) : congr_arg _ $ funext $ λ h, (calc
    h <$> (g <*> x)
        = g <*> x >>= pure ∘ h : eq.symm $ bind_pure_comp_eq_map _ _
    ... = g >>= (<$> x) >>= pure ∘ h                    : eq.rec rfl $ eq.symm $ bind_map_eq_seq g x
    ... = g >>= λ g, g <$> x >>= pure ∘ h               : bind_assoc _ _ _
    ... = g >>= λ g, pure (h ∘ g) >>= (<$> x)        : congr_arg _ $ funext $ λ g, (calc
      g <$> x >>= pure ∘ h
          = x >>= pure ∘ g >>= pure ∘ h        : eq.rec rfl $ eq.symm $ bind_pure_comp_eq_map g x
      ... = x >>= λ x, pure (g x) >>= pure ∘ h : bind_assoc _ _ _
      ... = x >>= λ x, pure (h (g x)) : congr_arg _ $ funext $ λ x, pure_bind _ _
      ... = (h ∘ g) <$> x : bind_pure_comp_eq_map _ _
      ... = pure (h ∘ g) >>= (<$> x) : eq.symm $ pure_bind _ _)
    ... = g >>= pure ∘ (@comp α β γ h) >>= (<$> x) : eq.symm $ bind_assoc _ _ _
    ... = @comp α β γ h <$> g >>= (<$> x) : eq.rec rfl $ bind_pure_comp_eq_map (comp h) g
    ... = pure (@comp α β γ h) >>= (<$> g) >>= (<$> x) : eq.rec rfl $ eq.symm $ pure_bind (@comp α β γ h) (<$> g))
  ... = h >>= (λ h, pure (@comp α β γ h) >>= (<$> g)) >>= (<$> x) : eq.symm $ bind_assoc _ _ _
  ... = h >>= pure ∘ @comp α β γ >>= (<$> g) >>= (<$> x) : eq.rec rfl $ eq.symm $ bind_assoc h (pure ∘ @comp α β γ) (<$> g)
  ... = (@comp α β γ <$> h) >>= (<$> g) >>= (<$> x) : eq.rec rfl $ bind_pure_comp_eq_map (@comp α β γ) h
  ... = ((@comp α β γ <$> h) >>= (<$> g)) <*> x : bind_map_eq_seq _ _
  ... = (@comp α β γ <$> h) <*> g <*> x : eq.rec rfl $ bind_map_eq_seq (@comp α β γ <$> h) g)
end

@[reducible] def return {m : Type u → Type v} [monad m] {α : Type u} : α → m α :=
pure

/- Identical to has_bind.and_then, but it is not inlined. -/
def has_bind.seq {α β : Type u} {m : Type u → Type v} [has_bind m] (x : m α) (y : m β) : m β :=
do x, y

-- monad "law" derivable from other laws
theorem monad.bind_pure {α β : Type u} {m : Type u → Type v} [monad m] (x : m α) : x >>= pure = x :=
eq.trans (monad.bind_pure_comp_eq_map _ _ _) (functor.id_map _)
