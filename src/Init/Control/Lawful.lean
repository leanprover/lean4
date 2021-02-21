/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.SimpLemmas
import Init.Control.Except

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
  comp_map g h x := by
    repeat rw [← pure_seq]
    simp [seq_assoc, map_pure, seq_pure]

export LawfulApplicative (seqLeft_eq seqRight_eq pure_seq map_pure seq_pure seq_assoc)

attribute [simp] map_pure seq_pure

@[simp] theorem pure_id_seq [Applicative f] [LawfulApplicative f] (x : f α) : pure id <*> x = x := by
  simp [pure_seq]

class LawfulMonad (m : Type u → Type v) [Monad m] extends LawfulApplicative m : Prop where
  bind_pure_comp (f : α → β) (x : m α) : x >>= pure ∘ f = f <$> x
  bind_map       (f : m (α → (β : Type u))) (x : m α) : f >>= (. <$> x) = f <*> x
  pure_bind      (x : α) (f : α → m β) : pure x >>= f = f x
  bind_assoc     (x : m α) (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= fun x => f x >>= g
  map_pure g x    := by rw [← bind_pure_comp, pure_bind]
  seq_pure g x    := by rw [← bind_map]; simp [map_pure, bind_pure_comp]
  seq_assoc x g h := by
    -- TODO: support for applying `symm` at `simp` arguments
    let bind_pure_comp_symm {α β : Type u} (f : α → β) (x : m α) : f <$> x = x >>= pure ∘ f := by
      rw [bind_pure_comp]
    let bind_map_symm {α β : Type u} (f : m (α → (β : Type u))) (x : m α) : f <*> x = f >>= (. <$> x) := by
      rw [bind_map]
    simp[bind_pure_comp_symm, bind_map_symm, bind_assoc, pure_bind]

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

/- Id -/

namespace Id

@[simp] theorem map_eq (x : Id α) (f : α → β) : f <$> x = f x := rfl
@[simp] theorem bind_eq (x : Id α) (f : α → id β) : x >>= f = f x := rfl
@[simp] theorem pure_eq (a : α) : (pure a : Id α) = a := rfl

instance : LawfulMonad Id := by
  refine! { .. } <;> intros <;> rfl

end Id

/- ExceptT -/

namespace ExceptT

theorem ext [Monad m] {x y : ExceptT ε m α} (h : x.run = y.run) : x = y := by
  simp [run] at h
  assumption

@[simp] theorem run_pure [Monad m] : run (pure x : ExceptT ε m α) = pure (Except.ok x) := rfl
@[simp] theorem run_lift [Monad m] : run (ExceptT.lift x : ExceptT ε m α) = Except.ok <$> x := rfl
@[simp] theorem run_throw [Monad m] : run (throw e : ExceptT ε m β) = pure (Except.error e) := rfl
@[simp] theorem run_bind [Monad m] (x : ExceptT ε m α)
        : run (x >>= f : ExceptT ε m β)
          =
          run x >>= fun
                     | Except.ok x => run (f x)
                     | Except.error e => pure (Except.error e) :=
  rfl

@[simp] theorem lift_pure [Monad m] [LawfulMonad m] (a : α) : ExceptT.lift (pure a) = (pure a : ExceptT ε m α) := by
  simp [ExceptT.lift, pure, ExceptT.pure]

@[simp] theorem run_map [Monad m] [LawfulMonad m] (f : α → β) (x : ExceptT ε m α)
    : (f <$> x).run = Except.map f <$> x.run := by
  rw [← bind_pure_comp (m := m)]
  simp [Functor.map, ExceptT.map]
  apply bind_congr
  intro a; cases a <;> simp [Except.map]

protected theorem seq_eq {α β ε : Type u} [Monad m] (mf : ExceptT ε m (α → β)) (x : ExceptT ε m α) : mf <*> x = mf >>= fun f => f <$> x :=
  rfl

protected theorem bind_pure_comp [Monad m] [LawfulMonad m] (f : α → β) (x : ExceptT ε m α) : x >>= pure ∘ f = f <$> x := by
  intros; rfl

protected theorem seqLeft_eq {α β ε : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] (x : ExceptT ε m α) (y : ExceptT ε m β) : x <* y = const β <$> x <*> y := by
  show (x >>= fun a => y >>= fun _ => pure a) = (const (α := α) β <$> x) >>= fun f => f <$> y
  rw [← ExceptT.bind_pure_comp]
  apply ext
  simp
  apply bind_congr
  intro a
  cases a with
  | error => simp
  | ok =>
    simp; rw [← bind_pure_comp]; apply bind_congr; intro b;
    cases b <;> simp [comp, Except.map, const]

protected theorem seqRight_eq [Monad m] [LawfulMonad m] (x : ExceptT ε m α) (y : ExceptT ε m β) : x *> y = const α id <$> x <*> y := by
  show (x >>= fun _ => y) = (const α id <$> x) >>= fun f => f <$> y
  rw [← ExceptT.bind_pure_comp]
  apply ext
  simp
  apply bind_congr
  intro a; cases a <;> simp

instance [Monad m] [LawfulMonad m] : LawfulMonad (ExceptT ε m) where
  id_map         := by intros; apply ext; simp
  map_const      := by intros; rfl
  seqLeft_eq     := ExceptT.seqLeft_eq
  seqRight_eq    := ExceptT.seqRight_eq
  pure_seq       := by intros; apply ext; simp [ExceptT.seq_eq]
  bind_pure_comp := ExceptT.bind_pure_comp
  bind_map       := by intros; rfl
  pure_bind      := by intros; apply ext; simp
  bind_assoc     := by intros; apply ext; simp; apply bind_congr; intro a; cases a <;> simp

end ExceptT
