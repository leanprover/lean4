/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.category.monad init.meta.interactive
import init.category.state
universes u v

open function
open tactic

meta def control_laws_tac := whnf_target >> intros >> to_expr ``(rfl) >>= exact

class is_lawful_functor (f : Type u → Type v) [functor f] : Prop :=
(map_const_eq : ∀ {α β : Type u}, @has_map.map_const f _ α β = (<$>) ∘ const β . control_laws_tac)
-- `functor` is indeed a categorical functor
(id_map       : Π {α : Type u} (x : f α), id <$> x = x)
(comp_map     : Π {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x)

export is_lawful_functor (map_const_eq id_map comp_map)
attribute [simp] id_map
-- `comp_map` does not make a good simp lemma

class is_lawful_applicative (f : Type u → Type v) [applicative f] extends is_lawful_functor f : Prop :=
(seq_left_eq  : ∀ {α β : Type u} (a : f α) (b : f β), a <* b = const β <$> a <*> b . control_laws_tac)
(seq_right_eq : ∀ {α β : Type u} (a : f α) (b : f β), a *> b = const α id <$> a <*> b . control_laws_tac)
-- applicative laws
(pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x)
(map_pure        : ∀ {α β : Type u} (g : α → β) (x : α), g <$> (pure x : f α) = pure (g x))
(seq_pure        : ∀ {α β : Type u} (g : f (α → β)) (x : α), g <*> pure x = (λ g : α → β, g x) <$> g)
(seq_assoc       : ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)), h <*> (g <*> x) = (@comp α β γ <$> h) <*> g <*> x)
-- default functor law
(comp_map := begin intros; simp [(pure_seq_eq_map _ _).symm, seq_assoc, map_pure, seq_pure] end)

export is_lawful_applicative (seq_left_eq seq_right_eq pure_seq_eq_map map_pure seq_pure seq_assoc)
attribute [simp] map_pure seq_pure

-- applicative "law" derivable from other laws
@[simp] theorem pure_id_seq {α : Type u} {f : Type u → Type v} [applicative f] [is_lawful_applicative f] (x : f α) : pure id <*> x = x :=
by simp [pure_seq_eq_map]

class is_lawful_monad (m : Type u → Type v) [monad m] extends is_lawful_applicative m : Prop :=
(bind_pure_comp_eq_map : ∀ {α β : Type u} (f : α → β) (x : m α), x >>= pure ∘ f = f <$> x  . control_laws_tac)
(bind_map_eq_seq : ∀ {α β : Type u} (f : m (α → β)) (x : m α), f >>= (<$> x) = f <*> x  . control_laws_tac)
-- monad laws
(pure_bind : ∀ {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x)
(bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),
  x >>= f >>= g = x >>= λ x, f x >>= g)
(pure_seq_eq_map := by intros; rw ←bind_map_eq_seq; simp [pure_bind])
(map_pure := by intros; rw ←bind_pure_comp_eq_map; simp [pure_bind])
(seq_pure := by intros; rw ←bind_map_eq_seq; simp [map_pure, bind_pure_comp_eq_map])
(seq_assoc := by intros; simp [(bind_pure_comp_eq_map _ _).symm,
                               (bind_map_eq_seq _ _).symm,
                               bind_assoc, pure_bind])

export is_lawful_monad (bind_pure_comp_eq_map bind_map_eq_seq pure_bind bind_assoc)
attribute [simp] pure_bind

-- monad "law" derivable from other laws
@[simp] theorem bind_pure {α : Type u} {m : Type u → Type v} [monad m] [is_lawful_monad m] (x : m α) : x >>= pure = x :=
show x >>= pure ∘ id = x, by rw bind_pure_comp_eq_map; simp [id_map]


-- instances of previously defined monads

instance (m : Type u → Type v) [monad m] [is_lawful_monad m] (σ : Type u) : is_lawful_monad (state_t σ m) :=
{ id_map := begin
    intros, funext,
    simp [(<$>), state_t.bind, state_t.return, function.comp, return],
    have h : state_t.bind._match_1 (λ (x : α) (s : σ), @pure m _ _ (x, s)) = pure,
    { funext s, cases s; refl },
    { simp [h, bind_pure] },
  end,
  pure_bind := begin
    intros, funext,
    simp [bind, pure, has_pure.pure, state_t.bind, state_t.return, pure_bind],
  end,
  bind_assoc := begin
    intros, funext,
    simp [bind, state_t.bind, state_t.return, bind_assoc],
    apply congr_arg, funext r,
    cases r, refl
  end, ..state_t.monad }
