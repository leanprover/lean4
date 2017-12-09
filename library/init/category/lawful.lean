/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.category.monad init.meta.interactive
universes u v

open function
open tactic

meta def control_laws_tac := whnf_target >> intros >> to_expr ``(rfl) >>= exact

class lawful_functor (f : Type u → Type v) extends functor f : Type (max (u+1) v) :=
(map_const_eq : ∀ {α β : Type u}, @map_const α β = map ∘ const β . control_laws_tac)
-- `functor` is indeed a categorical functor
(id_map       : Π {α : Type u} (x : f α), id <$> x = x)
(comp_map     : Π {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x)

export lawful_functor (map_const_eq id_map comp_map)
attribute [simp] id_map
-- `comp_map` does not make a good simp lemma

class lawful_applicative (f : Type u → Type v) extends applicative f :=
(seq_left_eq  : ∀ {α β : Type u} (a : f α) (b : f β), a <* b = const β <$> a <*> b . control_laws_tac)
(seq_right_eq : ∀ {α β : Type u} (a : f α) (b : f β), a *> b = const α id <$> a <*> b . control_laws_tac)
-- from `lawful_functor`
(map_const_eq : ∀ {α β : Type u}, @map_const α β = map ∘ const β . control_laws_tac)
(id_map       : Π {α : Type u} (x : f α), id <$> x = x)
-- applicative laws
(pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x) -- . control_laws_tac)
(map_pure        : ∀ {α β : Type u} (g : α → β) (x : α), g <$> pure x = pure (g x))
(seq_pure        : ∀ {α β : Type u} (g : f (α → β)) (x : α), g <*> pure x = (λ g : α → β, g x) <$> g)
(seq_assoc       : ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)), h <*> (g <*> x) = (@comp α β γ <$> h) <*> g <*> x)

export lawful_applicative (seq_left_eq seq_right_eq pure_seq_eq_map map_pure seq_pure seq_assoc)
attribute [simp] map_pure seq_pure

instance lawful_applicative.lawful_functor (f : Type u → Type v) [i : lawful_applicative f] : lawful_functor f :=
{ comp_map := by intros; simp [(pure_seq_eq_map _ _).symm, seq_assoc, map_pure], ..i }

-- applicative "law" derivable from other laws
@[simp] theorem pure_id_seq {α : Type u} {f : Type u → Type v} [lawful_applicative f] (x : f α) : pure id <*> x = x :=
by simp [pure_seq_eq_map]

class lawful_monad (m : Type u → Type v) extends monad m : Type (max (u+1) v) :=
(bind_pure_comp_eq_map : ∀ {α β : Type u} (f : α → β) (x : m α), x >>= pure ∘ f = f <$> x  . control_laws_tac)
(bind_map_eq_seq : ∀ {α β : Type u} (f : m (α → β)) (x : m α), f >>= (<$> x) = f <*> x  . control_laws_tac)
-- from `lawful_functor`
(map_const_eq : ∀ {α β : Type u}, @map_const α β = map ∘ const β . control_laws_tac)
(id_map       : Π {α : Type u} (x : m α), id <$> x = x)
-- from `lawful_applicative`
(seq_left_eq  : ∀ {α β : Type u} (a : m α) (b : m β), a <* b = const β <$> a <*> b . control_laws_tac)
(seq_right_eq : ∀ {α β : Type u} (a : m α) (b : m β), a *> b = const α id <$> a <*> b . control_laws_tac)
-- monad laws
(pure_bind : ∀ {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x)
(bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),
  x >>= f >>= g = x >>= λ x, f x >>= g)

export lawful_monad (bind_pure_comp_eq_map bind_map_eq_seq pure_bind bind_assoc)
attribute [simp] pure_bind

-- monad "law" derivable from other laws
@[simp] theorem bind_pure {α : Type u} {m : Type u → Type v} [lawful_monad m] (x : m α) : x >>= pure = x :=
show x >>= pure ∘ id = x, by rw bind_pure_comp_eq_map; simp [lawful_monad.id_map]

-- all applicative laws are derivable from the monad laws + id_map
instance lawful_monad.lawful_applicative (m : Type u → Type v) [i : lawful_monad m] : lawful_applicative m :=
have map_pure : ∀ {α β : Type u} (g : α → β) (x : α), g <$> (pure x : m _) = pure (g x),
by intros; rw ←bind_pure_comp_eq_map; simp [pure_bind],
{ pure_seq_eq_map := by intros; rw ←bind_map_eq_seq; simp,
  map_pure := @map_pure,
  seq_pure := by intros; rw ←bind_map_eq_seq; simp [map_pure, bind_pure_comp_eq_map],
  seq_assoc :=  λ α β γ x g h, calc
  h <*> (g <*> x)
      = h >>= (<$> g <*> x) : by rw bind_map_eq_seq
  ... = h >>= λ h, pure (@comp α β γ h) >>= (<$> g) >>= (<$> x) : congr_arg _ $ funext $ λ h, (calc
    h <$> (g <*> x)
        = g <*> x >>= pure ∘ h : by rw bind_pure_comp_eq_map
    ... = g >>= (<$> x) >>= pure ∘ h : by rw bind_map_eq_seq
    ... = g >>= λ g, g <$> x >>= pure ∘ h : by rw bind_assoc
    ... = g >>= λ g, pure (h ∘ g) >>= (<$> x)        : congr_arg _ $ funext $ λ g, (calc
      g <$> x >>= pure ∘ h
          = x >>= pure ∘ g >>= pure ∘ h        : by simp [bind_pure_comp_eq_map]
      ... = x >>= λ x, pure (g x) >>= pure ∘ h : by rw bind_assoc
      ... = x >>= λ x, pure (h (g x)) : by simp
      ... = (h ∘ g) <$> x : by rw bind_pure_comp_eq_map
      ... = pure (h ∘ g) >>= (<$> x) : by simp)
    ... = g >>= pure ∘ (@comp α β γ h) >>= (<$> x) : by rw bind_assoc
    ... = pure (@comp α β γ h) >>= (<$> g) >>= (<$> x) : by simp [bind_pure_comp_eq_map])
  ... = h >>= pure ∘ @comp α β γ >>= (<$> g) >>= (<$> x) : by simp [bind_assoc]
  ... = (@comp α β γ <$> h) >>= (<$> g) >>= (<$> x) : by simp [bind_pure_comp_eq_map]
  ... = (@comp α β γ <$> h) <*> g <*> x : by simp [bind_map_eq_seq],
  ..i }
