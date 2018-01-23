/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.category.monad init.meta.interactive
import init.category.state init.category.except init.category.reader
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

lemma bind_ext_congr {α β} {m : Type u → Type v} [has_bind m] {x : m α} {f : α → m β} (g : α → m β) :
  (∀ a, f a = g a) →
  x >>= f = x >>= g :=
λ h, have f = g, from funext h,
     by simp [this]

lemma map_ext_congr {α β} {m : Type u → Type v} [has_map m] {x : m α} {f : α → β} (g : α → β) :
  (∀ a, f a = g a) →
  (f <$> x : m β) = g <$> x :=
λ h, have f = g, from funext h,
     by simp [this]

-- instances of previously defined monads

namespace id
variables {α β : Type}
@[simp] lemma map_eq (x : id α) (f : α → β) : f <$> x = f x := rfl
@[simp] lemma bind_eq (x : id α) (f : α → id β) : x >>= f = f x := rfl
@[simp] lemma pure_eq (a : α) : (pure a : id α) = a := rfl
end id

instance : is_lawful_monad id :=
by refine { id_map := _, bind_assoc := _, pure_bind := _ };
   intros; refl

namespace state_t
section
  variable  {σ : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}
  variables (x : state_t σ m α) (st : σ)

  lemma ext {x x' : state_t σ m α} (h : ∀ st, x.run st = x'.run st) : x = x' :=
  by cases_type* state_t; simp [show x = x', from funext h]

  @[simp] lemma run_pure (a) : (pure a : state_t σ m α).run st = pure (a, st) := rfl
  @[simp] lemma run_bind (f : α → state_t σ m β) : (x >>= f).run st = x.run st >>= λ p, (f p.1).run p.2 :=
  by simp [bind, state_t.bind, state_t.run]; rw bind_ext_congr; intro a; cases a; simp [state_t.bind, state_t.run]
  @[simp] lemma run_map (f : α → β) [is_lawful_monad m] : (f <$> x).run st = (λ p : α × σ, (f (prod.fst p), prod.snd p)) <$> x.run st :=
  begin
    rw ←bind_pure_comp_eq_map m,
    change (x >>= pure ∘ f).run st = _,
    simp
  end
  @[simp] lemma run_monad_lift {n} [has_monad_lift_t n m] (x : n α) : (monad_lift x : state_t σ m α).run st = do a ← (monad_lift x : m α), pure (a, st) := rfl
  @[simp] lemma run_monad_map {m' n n'} [monad m'] [monad_functor_t n n' m m'] (f : ∀ {α}, n α → n' α) : (monad_map @f x : state_t σ m' α).run st = monad_map @f (x.run st) := rfl
  @[simp] lemma run_zoom {σ'} (st get set) : (state_t.zoom get set x : state_t σ' m α).run st = (λ p : α × σ, (p.1, set p.2 st)) <$> x.run (get st) := rfl
  @[simp] lemma run_get : (state_t.get : state_t σ m σ).run st = pure (st, st) := rfl
  @[simp] lemma run_put (st') : (state_t.put st' : state_t σ m _).run st = pure (punit.star, st') := rfl
end
end state_t

instance (m : Type u → Type v) [monad m] [is_lawful_monad m] (σ : Type u) : is_lawful_monad (state_t σ m) :=
{ id_map := by intros; apply state_t.ext; intro; simp; erw id_map,
  pure_bind := by intros; apply state_t.ext; intro; simp,
  bind_assoc := by intros; apply state_t.ext; intro; simp [bind_assoc] }


namespace except_t
  variables {α β ε : Type u} {m : Type u → Type v} [monad m] (x : except_t ε m α)

  lemma ext {x x' : except_t ε m α} (h : x.run = x'.run) : x = x' :=
  by cases_type* except_t; simp * at *

  @[simp] lemma run_pure (a) : (pure a : except_t ε m α).run = pure (@except.ok ε α a) := rfl
  @[simp] lemma run_bind (f : α → except_t ε m β) : (x >>= f).run = x.run >>= except_t.bind_cont f := rfl
  @[simp] lemma run_map (f : α → β) [is_lawful_monad m] : (f <$> x).run = except.map f <$> x.run :=
  begin
    rw ←bind_pure_comp_eq_map m,
    change (x >>= pure ∘ f).run = _,
    simp,
    rw [bind_ext_congr],
    intro a; cases a; simp [except_t.bind_cont, except.map]
  end
  @[simp] lemma run_monad_lift {n} [has_monad_lift_t n m] (x : n α) : (@monad_lift _ _ _ _ x : except_t ε m α).run = except.ok <$> (monad_lift x : m α) := rfl
  @[simp] lemma run_monad_map {m' n n'} [monad m'] [monad_functor_t n n' m m'] (f : ∀ {α}, n α → n' α) : (monad_map @f x : except_t ε m' α).run = monad_map @f x.run := rfl
end except_t

instance (m : Type u → Type v) [monad m] [is_lawful_monad m] (ε : Type u) : is_lawful_monad (except_t ε m) :=
{ id_map := begin
    intros, apply except_t.ext, simp,
    rw [map_ext_congr, id_map],
    intro a, cases a; refl
  end,
  bind_pure_comp_eq_map := begin
    intros, apply except_t.ext, simp,
    rw [bind_ext_congr, bind_pure_comp_eq_map],
    intro a, cases a; refl
  end,
  bind_assoc := begin
    intros, apply except_t.ext, simp [bind_assoc],
    rw [bind_ext_congr],
    { intro a, cases a; simp [except_t.bind_cont] }
  end,
  pure_bind := by intros; apply except_t.ext; simp [except_t.bind_cont] }


namespace reader_t
section
  variable  {r : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}
  variables (x : reader_t r m α) (cfg : r)

  lemma ext {x x' : reader_t r m α} (h : ∀ cfg, x.run cfg = x'.run cfg) : x = x' :=
  by cases_type* reader_t; simp [show x = x', from funext h]

  @[simp] lemma run_pure (a) : (pure a : reader_t r m α).run cfg = pure a := rfl
  @[simp] lemma run_bind (f : α → reader_t r m β) : (x >>= f).run cfg = x.run cfg >>= λ a, (f a).run cfg := rfl
  @[simp] lemma run_map (f : α → β) [is_lawful_monad m] : (f <$> x).run cfg = f <$> x.run cfg :=
  by rw ←bind_pure_comp_eq_map m; refl
  @[simp] lemma run_monad_lift {n} [has_monad_lift_t n m] (x : n α) : (@monad_lift _ _ _ _ x : reader_t r m α).run cfg = (monad_lift x : m α) := rfl
  @[simp] lemma run_monad_map {m' n n'} [monad m'] [monad_functor_t n n' m m'] (f : ∀ {α}, n α → n' α) : (monad_map @f x : reader_t r m' α).run cfg = monad_map @f (x.run cfg) := rfl
  @[simp] lemma run_read : (reader_t.read : reader_t r m r).run cfg = pure cfg := rfl
end
end reader_t

instance (r : Type u) (m : Type u → Type v) [monad m] [is_lawful_monad m] : is_lawful_monad (reader_t r m) :=
{ id_map := by intros; apply reader_t.ext; intro; simp,
  pure_bind := by intros; apply reader_t.ext; intro; simp,
  bind_assoc := by intros; apply reader_t.ext; intro; simp [bind_assoc] }
