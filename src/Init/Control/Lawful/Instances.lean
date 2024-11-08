/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Control.Lawful.Basic
import Init.Control.Except
import Init.Control.StateRef
import Init.Ext

open Function

/-! # ExceptT -/

namespace ExceptT

@[ext] theorem ext {x y : ExceptT ε m α} (h : x.run = y.run) : x = y := by
  simp [run] at h
  assumption

@[simp] theorem run_pure [Monad m] (x : α) : run (pure x : ExceptT ε m α) = pure (Except.ok x) := rfl

@[simp] theorem run_lift  [Monad.{u, v} m] (x : m α) : run (ExceptT.lift x : ExceptT ε m α) = (Except.ok <$> x : m (Except ε α)) := rfl

@[simp] theorem run_throw [Monad m] : run (throw e : ExceptT ε m β) = pure (Except.error e) := rfl

@[simp] theorem run_bind_lift [Monad m] [LawfulMonad m] (x : m α) (f : α → ExceptT ε m β) : run (ExceptT.lift x >>= f : ExceptT ε m β) = x >>= fun a => run (f a) := by
  simp [ExceptT.run, ExceptT.lift, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]

@[simp] theorem bind_throw [Monad m] [LawfulMonad m] (f : α → ExceptT ε m β) : (throw e >>= f) = throw e := by
  simp [throw, throwThe, MonadExceptOf.throw, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk]

theorem run_bind [Monad m] (x : ExceptT ε m α)
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
  simp [Functor.map, ExceptT.map, ←bind_pure_comp]
  apply bind_congr
  intro a; cases a <;> simp [Except.map]

protected theorem seq_eq {α β ε : Type u} [Monad m] (mf : ExceptT ε m (α → β)) (x : ExceptT ε m α) : mf <*> x = mf >>= fun f => f <$> x :=
  rfl

protected theorem bind_pure_comp [Monad m] (f : α → β) (x : ExceptT ε m α) : x >>= pure ∘ f = f <$> x := by
  intros; rfl

protected theorem seqLeft_eq {α β ε : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] (x : ExceptT ε m α) (y : ExceptT ε m β) : x <* y = const β <$> x <*> y := by
  show (x >>= fun a => y >>= fun _ => pure a) = (const (α := α) β <$> x) >>= fun f => f <$> y
  rw [← ExceptT.bind_pure_comp]
  apply ext
  simp [run_bind]
  apply bind_congr
  intro
  | Except.error _ => simp
  | Except.ok _ =>
    simp [←bind_pure_comp]; apply bind_congr; intro b;
    cases b <;> simp [comp, Except.map, const]

protected theorem seqRight_eq [Monad m] [LawfulMonad m] (x : ExceptT ε m α) (y : ExceptT ε m β) : x *> y = const α id <$> x <*> y := by
  show (x >>= fun _ => y) = (const α id <$> x) >>= fun f => f <$> y
  rw [← ExceptT.bind_pure_comp]
  apply ext
  simp [run_bind]
  apply bind_congr
  intro a; cases a <;> simp

instance [Monad m] [LawfulMonad m] : LawfulMonad (ExceptT ε m) where
  id_map         := by intros; apply ext; simp
  map_const      := by intros; rfl
  seqLeft_eq     := ExceptT.seqLeft_eq
  seqRight_eq    := ExceptT.seqRight_eq
  pure_seq       := by intros; apply ext; simp [ExceptT.seq_eq, run_bind]
  bind_pure_comp := ExceptT.bind_pure_comp
  bind_map       := by intros; rfl
  pure_bind      := by intros; apply ext; simp [run_bind]
  bind_assoc     := by intros; apply ext; simp [run_bind]; apply bind_congr; intro a; cases a <;> simp

@[simp] theorem map_throw [Monad m] [LawfulMonad m] {α β : Type _} (f : α → β) (e : ε) :
    f <$> (throw e : ExceptT ε m α) = (throw e : ExceptT ε m β) := by
  simp only [ExceptT.instMonad, ExceptT.map, ExceptT.mk, throw, throwThe, MonadExceptOf.throw,
    pure_bind]

end ExceptT

/-! # Except -/

instance : LawfulMonad (Except ε) := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun a _ _ => by cases a <;> rfl)

instance : LawfulApplicative (Except ε) := inferInstance
instance : LawfulFunctor (Except ε) := inferInstance

/-! # ReaderT -/

namespace ReaderT

@[ext] theorem ext {x y : ReaderT ρ m α} (h : ∀ ctx, x.run ctx = y.run ctx) : x = y := by
  simp [run] at h
  exact funext h

@[simp] theorem run_pure [Monad m] (a : α) (ctx : ρ) : (pure a : ReaderT ρ m α).run ctx = pure a := rfl

@[simp] theorem run_bind [Monad m] (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) (ctx : ρ)
    : (x >>= f).run ctx = x.run ctx >>= λ a => (f a).run ctx := rfl

@[simp] theorem run_mapConst [Monad m] (a : α) (x : ReaderT ρ m β) (ctx : ρ)
    : (Functor.mapConst a x).run ctx = Functor.mapConst a (x.run ctx) := rfl

@[simp] theorem run_map [Monad m] (f : α → β) (x : ReaderT ρ m α) (ctx : ρ)
    : (f <$> x).run ctx = f <$> x.run ctx := rfl

@[simp] theorem run_monadLift [MonadLiftT n m] (x : n α) (ctx : ρ)
    : (monadLift x : ReaderT ρ m α).run ctx = (monadLift x : m α) := rfl

@[simp] theorem run_monadMap [MonadFunctor n m] (f : {β : Type u} → n β → n β) (x : ReaderT ρ m α) (ctx : ρ)
    : (monadMap @f x : ReaderT ρ m α).run ctx = monadMap @f (x.run ctx) := rfl

@[simp] theorem run_read [Monad m] (ctx : ρ) : (ReaderT.read : ReaderT ρ m ρ).run ctx = pure ctx := rfl

@[simp] theorem run_seq {α β : Type u} [Monad m] (f : ReaderT ρ m (α → β)) (x : ReaderT ρ m α) (ctx : ρ)
    : (f <*> x).run ctx = (f.run ctx <*> x.run ctx) := rfl

@[simp] theorem run_seqRight [Monad m] (x : ReaderT ρ m α) (y : ReaderT ρ m β) (ctx : ρ)
    : (x *> y).run ctx = (x.run ctx *> y.run ctx) := rfl

@[simp] theorem run_seqLeft [Monad m] (x : ReaderT ρ m α) (y : ReaderT ρ m β) (ctx : ρ)
    : (x <* y).run ctx = (x.run ctx <* y.run ctx) := rfl

instance [Monad m] [LawfulFunctor m] : LawfulFunctor (ReaderT ρ m) where
  id_map    := by intros; apply ext; simp
  map_const := by intros; funext a b; apply ext; intros; simp [map_const]
  comp_map  := by intros; apply ext; intros; simp [comp_map]

instance [Monad m] [LawfulApplicative m] : LawfulApplicative (ReaderT ρ m) where
  seqLeft_eq  := by intros; apply ext; intros; simp [seqLeft_eq]
  seqRight_eq := by intros; apply ext; intros; simp [seqRight_eq]
  pure_seq    := by intros; apply ext; intros; simp [pure_seq]
  map_pure    := by intros; apply ext; intros; simp [map_pure]
  seq_pure    := by intros; apply ext; intros; simp [seq_pure]
  seq_assoc   := by intros; apply ext; intros; simp [seq_assoc]

instance [Monad m] [LawfulMonad m] : LawfulMonad (ReaderT ρ m) where
  bind_pure_comp := by intros; apply ext; intros; simp [LawfulMonad.bind_pure_comp]
  bind_map       := by intros; apply ext; intros; simp [bind_map]
  pure_bind      := by intros; apply ext; intros; simp
  bind_assoc     := by intros; apply ext; intros; simp

end ReaderT

/-! # StateRefT -/

instance [Monad m] [LawfulMonad m] : LawfulMonad (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulMonad (ReaderT (ST.Ref ω σ) m))

/-! # StateT -/

namespace StateT

@[ext] theorem ext {x y : StateT σ m α} (h : ∀ s, x.run s = y.run s) : x = y :=
  funext h

@[simp] theorem run'_eq [Monad m] (x : StateT σ m α) (s : σ) : run' x s = (·.1) <$> run x s :=
  rfl

@[simp] theorem run_pure [Monad m] (a : α) (s : σ) : (pure a : StateT σ m α).run s = pure (a, s) := rfl

@[simp] theorem run_bind [Monad m] (x : StateT σ m α) (f : α → StateT σ m β) (s : σ)
    : (x >>= f).run s = x.run s >>= λ p => (f p.1).run p.2 := by
  simp [bind, StateT.bind, run]

@[simp] theorem run_map {α β σ : Type u} [Monad m] [LawfulMonad m] (f : α → β) (x : StateT σ m α) (s : σ) : (f <$> x).run s = (fun (p : α × σ) => (f p.1, p.2)) <$> x.run s := by
  simp [Functor.map, StateT.map, run, ←bind_pure_comp]

@[simp] theorem run_get [Monad m] (s : σ)    : (get : StateT σ m σ).run s = pure (s, s) := rfl

@[simp] theorem run_set [Monad m] (s s' : σ) : (set s' : StateT σ m PUnit).run s = pure (⟨⟩, s') := rfl

@[simp] theorem run_modify [Monad m] (f : σ → σ) (s : σ) : (modify f : StateT σ m PUnit).run s = pure (⟨⟩, f s) := rfl

@[simp] theorem run_modifyGet [Monad m] (f : σ → α × σ) (s : σ) : (modifyGet f : StateT σ m α).run s = pure ((f s).1, (f s).2) := by
  simp [modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, run]

@[simp] theorem run_lift {α σ : Type u} [Monad m] (x : m α) (s : σ) : (StateT.lift x : StateT σ m α).run s = x >>= fun a => pure (a, s) := rfl

theorem run_bind_lift {α σ : Type u} [Monad m] [LawfulMonad m] (x : m α) (f : α → StateT σ m β) (s : σ) : (StateT.lift x >>= f).run s = x >>= fun a => (f a).run s := by
  simp [StateT.lift, StateT.run, bind, StateT.bind]

@[simp] theorem run_monadLift {α σ : Type u} [Monad m] [MonadLiftT n m] (x : n α) (s : σ) : (monadLift x : StateT σ m α).run s = (monadLift x : m α) >>= fun a => pure (a, s) := rfl

@[simp] theorem run_monadMap [MonadFunctor n m] (f : {β : Type u} → n β → n β) (x : StateT σ m α) (s : σ) :
    (monadMap @f x : StateT σ m α).run s = monadMap @f (x.run s) := rfl

@[simp] theorem run_seq {α β σ : Type u} [Monad m] [LawfulMonad m] (f : StateT σ m (α → β)) (x : StateT σ m α) (s : σ) : (f <*> x).run s = (f.run s >>= fun fs => (fun (p : α × σ) => (fs.1 p.1, p.2)) <$> x.run fs.2) := by
  show (f >>= fun g => g <$> x).run s = _
  simp

@[simp] theorem run_seqRight [Monad m] (x : StateT σ m α) (y : StateT σ m β) (s : σ) : (x *> y).run s = (x.run s >>= fun p => y.run p.2) := by
  show (x >>= fun _ => y).run s = _
  simp

@[simp] theorem run_seqLeft {α β σ : Type u} [Monad m] (x : StateT σ m α) (y : StateT σ m β) (s : σ) : (x <* y).run s = (x.run s >>= fun p => y.run p.2 >>= fun p' => pure (p.1, p'.2)) := by
  show (x >>= fun a => y >>= fun _ => pure a).run s = _
  simp

theorem seqRight_eq [Monad m] [LawfulMonad m] (x : StateT σ m α) (y : StateT σ m β) : x *> y = const α id <$> x <*> y := by
  apply ext; intro s
  simp [←bind_pure_comp, const]
  apply bind_congr; intro p; cases p
  simp [Prod.eta]

theorem seqLeft_eq [Monad m] [LawfulMonad m] (x : StateT σ m α) (y : StateT σ m β) : x <* y = const β <$> x <*> y := by
  apply ext; intro s
  simp [←bind_pure_comp]

instance [Monad m] [LawfulMonad m] : LawfulMonad (StateT σ m) where
  id_map         := by intros; apply ext; intros; simp[Prod.eta]
  map_const      := by intros; rfl
  seqLeft_eq     := seqLeft_eq
  seqRight_eq    := seqRight_eq
  pure_seq       := by intros; apply ext; intros; simp
  bind_pure_comp := by intros; apply ext; intros; simp
  bind_map       := by intros; rfl
  pure_bind      := by intros; apply ext; intros; simp
  bind_assoc     := by intros; apply ext; intros; simp

end StateT

/-! # EStateM -/

instance : LawfulMonad (EStateM ε σ) := .mk'
  (id_map := fun x => funext <| fun s => by
    dsimp only [EStateM.instMonad, EStateM.map]
    match x s with
    | .ok _ _ => rfl
    | .error _ _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => funext <| fun s => by
    dsimp only [EStateM.instMonad, EStateM.bind]
    match x s with
    | .ok _ _ => rfl
    | .error _ _ => rfl)
  (map_const := fun _ _ => rfl)
