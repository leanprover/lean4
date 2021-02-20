/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.SimpLemmas

open Function

class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  map_const          : (Functor.mapConst : α → f β → f α) = Functor.map ∘ const β
  id_map   (x : f α) : id <$> x = x
  comp_map (g : α → β) (h : β → γ) (x : f α) : (h ∘ g) <$> x = h <$> g <$> x

export LawfulFunctor (map_const id_map comp_map)

attribute [simp] id_map

class LawfulApplicative (f : Type u → Type v) [Applicative f] extends LawfulFunctor f : Prop where
  seqLeft_eq  (x : f α) (y : f β)     : x <* y = const β <$> x <*> y
  seqRight_eq (x : f α) (y : f β)     : x *> y = const α id <$> x <*> y
  pure_seq    (g : α → β) (x : f α)   : pure g <*> x = g <$> x
  map_pure    (g : α → β) (x : α)     : g <$> (pure x : f α) = pure (g x)
  seq_pure    (g : f (α → β)) (x : α) : g <*> pure x = (fun h : α → β => h x) <$> g
  seq_assoc   (x : f α) (g : f (α → β)) (h : f (β → γ)) : h <*> (g <*> x) = (@comp α β γ <$> h) <*> g <*> x

export LawfulApplicative (seqLeft_eq seqRight_eq pure_seq map_pure seq_pure seq_assoc)

attribute [simp] map_pure seq_pure

@[simp] theorem pure_id_seq [Applicative f] [LawfulApplicative f] (x : f α) : pure id <*> x = x := by
  simp [pure_seq]

class LawfulMonad (m : Type u → Type v) [Monad m] extends LawfulApplicative m : Prop where
  bind_pure_comp (f : α → β) (x : m α) : x >>= pure ∘ f = f <$> x
  bind_map       (f : m (α → (β : Type u))) (x : m α) : f >>= (. <$> x) = f <*> x
  pure_bind      (x : α) (f : α → m β) : pure x >>= f = f x
  bind_assoc     (x : m α) (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= fun x => f x >>= g

export LawfulMonad (bind_pure_comp bind_map pure_bind bind_assoc)
attribute [simp] pure_bind bind_assoc

@[simp] theorem bind_pure [Monad m] [LawfulMonad m] (x : m α) : x >>= pure = x := by
  show x >>= pure ∘ id = x
  rw [bind_pure_comp, id_map]

theorem map_eq_pure_bind [Monad m] [LawfulMonad m] (f : α → β) (x : m α) : f <$> x = x >>= fun a => pure (f a) := by
  rw [← bind_pure_comp]

theorem bind_congr [Bind m] {x : m α} {f g : α → m β} (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  simp [funext h]

theorem map_congr [Functor m] {x : m α} {f g : α → β} (h : ∀ a, f a = g a) : (f <$> x : m β) = g <$> x := by
  simp [funext h]
