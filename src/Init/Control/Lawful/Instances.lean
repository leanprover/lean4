/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Control.Lawful.Basic
import all Init.Control.Except
public import Init.Control.Option
import all Init.Control.Option
import all Init.Control.State
public import Init.Control.StateRef

public section

open Function

@[simp, grind =] theorem monadMap_refl {m : Type _ → Type _} {α} (f : ∀ {α}, m α → m α) :
    monadMap @f = @f α := rfl

/-! # ExceptT -/

namespace ExceptT

@[ext, grind ext] theorem ext {x y : ExceptT ε m α} (h : x.run = y.run) : x = y := by
  simp [run] at h
  assumption

@[simp, grind =] theorem run_mk (x : m (Except ε α)) : run (mk x : ExceptT ε m α) = x := rfl

@[simp, grind =] theorem run_pure [Monad m] (x : α) : run (pure x : ExceptT ε m α) = pure (Except.ok x) := rfl

@[simp, grind =] theorem run_lift  [Monad.{u, v} m] (x : m α) : run (ExceptT.lift x : ExceptT ε m α) = (Except.ok <$> x : m (Except ε α)) := rfl

@[simp, grind =] theorem run_throw [Monad m] : run (throw e : ExceptT ε m β) = pure (Except.error e) := rfl

@[simp, grind =] theorem run_bind_lift [Monad m] [LawfulMonad m] (x : m α) (f : α → ExceptT ε m β) : run (ExceptT.lift x >>= f : ExceptT ε m β) = x >>= fun a => run (f a) := by
  simp [ExceptT.run, ExceptT.lift, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]

@[simp, grind =] theorem bind_throw [Monad m] [LawfulMonad m] (f : α → ExceptT ε m β) : (throw e >>= f) = throw e := by
  simp [throw, throwThe, MonadExceptOf.throw, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk]

@[grind =]
theorem run_bind [Monad m] (x : ExceptT ε m α) (f : α → ExceptT ε m β)
        : run (x >>= f : ExceptT ε m β)
          =
          run x >>= fun
                     | Except.ok x => run (f x)
                     | Except.error e => pure (Except.error e) :=
  rfl

@[simp, grind =] theorem lift_pure [Monad m] [LawfulMonad m] (a : α) : ExceptT.lift (pure a) = (pure a : ExceptT ε m α) := by
  simp [ExceptT.lift, pure, ExceptT.pure]

@[simp, grind =] theorem run_map [Monad m] [LawfulMonad m] (f : α → β) (x : ExceptT ε m α)
    : (f <$> x).run = Except.map f <$> x.run := by
  simp [Functor.map, ExceptT.map, ←bind_pure_comp]
  apply bind_congr
  intro a; cases a <;> simp [Except.map]

@[simp, grind =] theorem run_monadMap [MonadFunctorT n m] (f : {β : Type u} → n β → n β) (x : ExceptT ε m α)
    : (monadMap @f x : ExceptT ε m α).run = monadMap @f (x.run) := rfl

protected theorem seq_eq {α β ε : Type u} [Monad m] (mf : ExceptT ε m (α → β)) (x : ExceptT ε m α) : mf <*> x = mf >>= fun f => f <$> x :=
  rfl

protected theorem bind_pure_comp [Monad m] (f : α → β) (x : ExceptT ε m α) : x >>= pure ∘ f = f <$> x := by
  intros; rfl

protected theorem seqLeft_eq {α β ε : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] (x : ExceptT ε m α) (y : ExceptT ε m β) : x <* y = const β <$> x <*> y := by
  change (x >>= fun a => y >>= fun _ => pure a) = (const (α := α) β <$> x) >>= fun f => f <$> y
  rw [← ExceptT.bind_pure_comp]
  apply ext
  simp [run_bind]
  apply bind_congr
  intro
  | Except.error _ => simp
  | Except.ok _ =>
    simp [←bind_pure_comp]; apply bind_congr; intro b;
    cases b <;> simp [Except.map, const]

protected theorem seqRight_eq [Monad m] [LawfulMonad m] (x : ExceptT ε m α) (y : ExceptT ε m β) : x *> y = const α id <$> x <*> y := by
  change (x >>= fun _ => y) = (const α id <$> x) >>= fun f => f <$> y
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

/-! Note that the `MonadControl` instance for `ExceptT` is not monad-generic. -/

@[simp] theorem run_restoreM [Monad m] (x : stM m (ExceptT ε m) α) :
    ExceptT.run (restoreM x) = pure x := rfl

@[simp] theorem run_liftWith [Monad m] (f : ({β : Type u} → ExceptT ε m β → m (stM m (ExceptT ε m) β)) → m α) :
    ExceptT.run (liftWith f) = Except.ok <$> (f fun x => x.run) :=
  rfl

@[simp] theorem run_controlAt [Monad m] [LawfulMonad m] (f : ({β : Type u} → ExceptT ε m β → m (stM m (ExceptT ε m) β)) → m (stM m (ExceptT ε m) α)) :
    ExceptT.run (controlAt m f) = f fun x => x.run := by
  simp [controlAt, run_bind, bind_map_left]

@[simp] theorem run_control [Monad m] [LawfulMonad m] (f : ({β : Type u} → ExceptT ε m β → m (stM m (ExceptT ε m) β)) → m (stM m (ExceptT ε m) α)) :
    ExceptT.run (control f) = f fun x => x.run := run_controlAt f

end ExceptT

/-! # Except -/

instance : LawfulMonad (Except ε) := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => by rfl)
  (bind_assoc := fun a _ _ => by cases a <;> rfl)

instance : LawfulApplicative (Except ε) := inferInstance
instance : LawfulFunctor (Except ε) := inferInstance

/-! # OptionT -/

namespace OptionT

@[ext] theorem ext {x y : OptionT m α} (h : x.run = y.run) : x = y := by
  simp [run] at h
  assumption

@[simp, grind =] theorem run_mk {m : Type u → Type v} (x : m (Option α)) :
    OptionT.run (OptionT.mk x) = x := by rfl

@[simp, grind =] theorem run_pure [Monad m] (x : α) : run (pure x : OptionT m α) = pure (some x) := by
  simp [run, pure, OptionT.pure, OptionT.mk]

@[simp, grind =] theorem run_lift  [Monad.{u, v} m] (x : m α) : run (OptionT.lift x : OptionT m α) = (return some (← x) : m (Option α)) := by
  simp [run, OptionT.lift, OptionT.mk]

@[simp, grind =] theorem run_throw [Monad m] : run (throw e : OptionT m β) = pure none := by
  simp [run, throw, throwThe, MonadExceptOf.throw, OptionT.fail, OptionT.mk]

@[simp, grind =] theorem run_bind_lift [Monad m] [LawfulMonad m] (x : m α) (f : α → OptionT m β) : run (OptionT.lift x >>= f : OptionT m β) = x >>= fun a => run (f a) := by
  simp [OptionT.run, OptionT.lift, bind, OptionT.bind, OptionT.mk]

@[simp, grind =] theorem bind_throw [Monad m] [LawfulMonad m] (f : α → OptionT m β) : (throw e >>= f) = throw e := by
  simp [throw, throwThe, MonadExceptOf.throw, bind, OptionT.bind, OptionT.mk, OptionT.fail]

@[simp, grind =] theorem run_bind (f : α → OptionT m β) [Monad m] :
    (x >>= f).run = Option.elimM x.run (pure none) (fun x => (f x).run) := by
  change x.run >>= _ = _
  simp [Option.elimM]
  exact bind_congr fun |some _ => rfl | none => rfl

@[simp, grind =] theorem lift_pure [Monad m] [LawfulMonad m] {α : Type u} (a : α) : OptionT.lift (pure a : m α) = pure a := by
  simp only [OptionT.lift, OptionT.mk, bind_pure_comp, map_pure, pure, OptionT.pure]

@[simp, grind =] theorem run_map [Monad m] [LawfulMonad m] (f : α → β) (x : OptionT m α)
    : (f <$> x).run = Option.map f <$> x.run := by
  simp [Functor.map, Option.map, ←bind_pure_comp]
  apply bind_congr
  intro a; cases a <;> simp [OptionT.pure, OptionT.mk]

@[simp, grind =] theorem run_monadMap [MonadFunctorT n m] (f : {β : Type u} → n β → n β) (x : OptionT m α)
    : (monadMap @f x : OptionT m α).run = monadMap @f (x.run) := rfl

protected theorem seq_eq {α β : Type u} [Monad m] (mf : OptionT m (α → β)) (x : OptionT m α) : mf <*> x = mf >>= fun f => f <$> x :=
  rfl

protected theorem bind_pure_comp [Monad m] (f : α → β) (x : OptionT m α) : x >>= pure ∘ f = f <$> x := by
  intros; rfl

protected theorem seqLeft_eq {α β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) : x <* y = const β <$> x <*> y := by
  change (x >>= fun a => y >>= fun _ => pure a) = (const (α := α) β <$> x) >>= fun f => f <$> y
  rw [← OptionT.bind_pure_comp]
  apply ext
  simp [Option.elimM, Option.elim]
  apply bind_congr
  intro
  | none => simp
  | some _ =>
    simp [←bind_pure_comp]; apply bind_congr; intro b;
    cases b <;> simp [const]

protected theorem seqRight_eq [Monad m] [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) : x *> y = const α id <$> x <*> y := by
  change (x >>= fun _ => y) = (const α id <$> x) >>= fun f => f <$> y
  rw [← OptionT.bind_pure_comp]
  apply ext
  simp [Option.elimM, Option.elim]
  apply bind_congr
  intro a; cases a <;> simp

instance [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m) where
  id_map         := by intros; apply ext; simp
  map_const      := by intros; rfl
  seqLeft_eq     := OptionT.seqLeft_eq
  seqRight_eq    := OptionT.seqRight_eq
  pure_seq       := by intros; apply ext; simp [OptionT.seq_eq, Option.elimM, Option.elim]
  bind_pure_comp := OptionT.bind_pure_comp
  bind_map       := by intros; rfl
  pure_bind      := by intros; apply ext; simp [Option.elimM, Option.elim]
  bind_assoc     := by intros; apply ext; simp [Option.elimM, Option.elim]; apply bind_congr; intro a; cases a <;> simp

@[simp] theorem run_seq [Monad m] [LawfulMonad m] (f : OptionT m (α → β)) (x : OptionT m α) :
    (f <*> x).run = Option.elimM f.run (pure none) (fun f => Option.map f <$> x.run) := by
  simp [seq_eq_bind_map, Option.elimM, Option.elim]

@[simp] theorem run_seqLeft [Monad m] [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) :
    (x <* y).run = Option.elimM x.run (pure none)
      (fun x => Option.map (Function.const β x) <$> y.run) := by
  simp [seqLeft_eq, seq_eq_bind_map, Option.elimM, OptionT.run_bind]

@[simp] theorem run_seqRight [Monad m] [LawfulMonad m] (x : OptionT m α) (y : OptionT m β) :
    (x *> y).run = Option.elimM x.run (pure none) (Function.const α y.run) := by
  simp only [seqRight_eq, run_seq, Option.elimM, run_map, Option.elim, bind_map_left]
  refine bind_congr (fun | some _ => by simp | none => by simp)

@[simp, grind =] theorem run_failure [Monad m] : (failure : OptionT m α).run = pure none := by rfl

@[simp] theorem map_failure [Monad m] [LawfulMonad m] {α β : Type _} (f : α → β) :
    f <$> (failure : OptionT m α) = (failure : OptionT m β) := by
  simp [OptionT.mk, Functor.map, Alternative.failure, OptionT.fail, OptionT.bind]

@[simp] theorem run_orElse [Monad m] (x : OptionT m α) (y : OptionT m α) :
    (x <|> y).run = Option.elimM x.run y.run (fun x => pure (some x)) :=
  bind_congr fun | some _ => by rfl | none => by rfl

/-! Note that the `MonadControl` instance for `OptionT` is not monad-generic. -/

@[simp] theorem run_restoreM [Monad m] (x : stM m (OptionT m) α) :
    OptionT.run (restoreM x) = pure x := rfl

@[simp] theorem run_liftWith [Monad m] [LawfulMonad m] (f : ({β : Type u} → OptionT m β → m (stM m (OptionT m) β)) → m α) :
    OptionT.run (liftWith f) = Option.some <$> (f fun x => x.run) := by
  dsimp [liftWith]
  rw [← bind_pure_comp]
  rfl

@[simp] theorem run_controlAt [Monad m] [LawfulMonad m] (f : ({β : Type u} → OptionT m β → m (stM m (OptionT m) β)) → m (stM m (OptionT m) α)) :
    OptionT.run (controlAt m f) = f fun x => x.run := by
  simp [controlAt, Option.elimM, Option.elim]

@[simp] theorem run_control [Monad m] [LawfulMonad m] (f : ({β : Type u} → OptionT m β → m (stM m (OptionT m) β)) → m (stM m (OptionT m) α)) :
    OptionT.run (control f) = f fun x => x.run := run_controlAt f

end OptionT

/-! # Option -/

instance : LawfulMonad Option := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => by rfl)
  (bind_assoc := fun a _ _ => by cases a <;> rfl)
  (bind_pure_comp := fun _ x => by cases x <;> rfl)

instance : LawfulApplicative Option := inferInstance
instance : LawfulFunctor Option := inferInstance

/-! # ReaderT -/

namespace ReaderT

@[ext, grind ext] theorem ext {x y : ReaderT ρ m α} (h : ∀ ctx, x.run ctx = y.run ctx) : x = y := by
  simp [run] at h
  exact funext h

@[simp, grind =] theorem run_mk (x : ρ → m α) (ctx : ρ) : run (.mk x : ReaderT ρ m α) ctx = x ctx :=
  rfl

@[simp, grind =] theorem run_pure [Monad m] (a : α) (ctx : ρ) : (pure a : ReaderT ρ m α).run ctx = pure a := rfl

@[simp, grind =] theorem run_bind [Monad m] (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) (ctx : ρ)
    : (x >>= f).run ctx = x.run ctx >>= λ a => (f a).run ctx := rfl

@[simp, grind =] theorem run_mapConst [Monad m] (a : α) (x : ReaderT ρ m β) (ctx : ρ)
    : (Functor.mapConst a x).run ctx = Functor.mapConst a (x.run ctx) := rfl

@[simp, grind =] theorem run_map [Monad m] (f : α → β) (x : ReaderT ρ m α) (ctx : ρ)
    : (f <$> x).run ctx = f <$> x.run ctx := rfl

@[simp, grind =] theorem run_monadLift [MonadLiftT n m] (x : n α) (ctx : ρ)
    : (monadLift x : ReaderT ρ m α).run ctx = (monadLift x : m α) := rfl

@[simp, grind =] theorem run_monadMap [MonadFunctorT n m] (f : {β : Type u} → n β → n β) (x : ReaderT ρ m α) (ctx : ρ)
    : (monadMap @f x : ReaderT ρ m α).run ctx = monadMap @f (x.run ctx) := rfl

@[simp, grind =] theorem run_read [Monad m] (ctx : ρ) : (ReaderT.read : ReaderT ρ m ρ).run ctx = pure ctx := rfl

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

/-! Note that the `MonadControl` instance for `ReaderT` is not monad-generic. -/

@[simp] theorem run_restoreM [Monad m] (x : stM m (ReaderT ρ m) α) (ctx : ρ) :
    ReaderT.run (restoreM x) ctx = pure x := rfl

@[simp] theorem run_liftWith [Monad m] (f : ({β : Type u} → ReaderT ρ m β → m (stM m (ReaderT ρ m) β)) → m α) (ctx : ρ) :
    ReaderT.run (liftWith f) ctx = (f fun x => x.run ctx) :=
  rfl

@[simp] theorem run_controlAt [Monad m] [LawfulMonad m] (f : ({β : Type u} → ReaderT ρ m β → m (stM m (ReaderT ρ m) β)) → m (stM m (ReaderT ρ m) α)) (ctx : ρ) :
    ReaderT.run (controlAt m f) ctx = f fun x => x.run ctx := by
  simp [controlAt]

@[simp] theorem run_control [Monad m] [LawfulMonad m] (f : ({β : Type u} → ReaderT ρ m β → m (stM m (ReaderT ρ m) β)) → m (stM m (ReaderT ρ m) α)) (ctx : ρ) :
    ReaderT.run (control f) ctx = f fun x => x.run ctx := run_controlAt f ctx

end ReaderT

/-! # StateRefT -/

instance [Monad m] [LawfulMonad m] : LawfulMonad (StateRefT' ω σ m) :=
  inferInstanceAs (LawfulMonad (ReaderT (ST.Ref ω σ) m))

/-! # StateT -/

namespace StateT

@[ext, grind ext] theorem ext {x y : StateT σ m α} (h : ∀ s, x.run s = y.run s) : x = y :=
  funext h

@[simp, grind =] theorem run_mk [Monad m] (x : σ → m (α × σ)) (s : σ) : run (.mk x) s = x s :=
  rfl

@[simp, grind =] theorem run'_eq [Monad m] (x : StateT σ m α) (s : σ) : run' x s = (·.1) <$> run x s :=
  rfl

@[simp, grind =] theorem run_pure [Monad m] (a : α) (s : σ) : (pure a : StateT σ m α).run s = pure (a, s) := rfl

@[simp, grind =] theorem run_bind [Monad m] (x : StateT σ m α) (f : α → StateT σ m β) (s : σ)
    : (x >>= f).run s = x.run s >>= λ p => (f p.1).run p.2 := rfl

@[simp, grind =] theorem run_map {α β σ : Type u} [Monad m] [LawfulMonad m] (f : α → β) (x : StateT σ m α) (s : σ) : (f <$> x).run s = (fun (p : α × σ) => (f p.1, p.2)) <$> x.run s := by
  rw [← bind_pure_comp (m := m)]
  rfl

@[simp, grind =] theorem run_get [Monad m] (s : σ)    : (get : StateT σ m σ).run s = pure (s, s) := rfl

@[simp, grind =] theorem run_set [Monad m] (s s' : σ) : (set s' : StateT σ m PUnit).run s = pure (⟨⟩, s') := rfl

@[simp, grind =] theorem run_modify [Monad m] (f : σ → σ) (s : σ) : (modify f : StateT σ m PUnit).run s = pure (⟨⟩, f s) := rfl

@[simp, grind =] theorem run_modifyGet [Monad m] (f : σ → α × σ) (s : σ) : (modifyGet f : StateT σ m α).run s = pure ((f s).1, (f s).2) := by
  rfl

@[simp, grind =] theorem run_lift {α σ : Type u} [Monad m] (x : m α) (s : σ) : (StateT.lift x : StateT σ m α).run s = x >>= fun a => pure (a, s) := rfl

@[grind =]
theorem run_bind_lift {α σ : Type u} [Monad m] [LawfulMonad m] (x : m α) (f : α → StateT σ m β) (s : σ) : (StateT.lift x >>= f).run s = x >>= fun a => (f a).run s := by
  simp

@[simp, grind =] theorem run_monadLift {α σ : Type u} [Monad m] [MonadLiftT n m] (x : n α) (s : σ) : (monadLift x : StateT σ m α).run s = (monadLift x : m α) >>= fun a => pure (a, s) := rfl

@[simp, grind =] theorem run_monadMap [MonadFunctorT n m] (f : {β : Type u} → n β → n β) (x : StateT σ m α) (s : σ) :
    (monadMap @f x : StateT σ m α).run s = monadMap @f (x.run s) := rfl

@[simp] theorem run_seq {α β σ : Type u} [Monad m] [LawfulMonad m] (f : StateT σ m (α → β)) (x : StateT σ m α) (s : σ) : (f <*> x).run s = (f.run s >>= fun fs => (fun (p : α × σ) => (fs.1 p.1, p.2)) <$> x.run fs.2) := by
  change (f >>= fun g => g <$> x).run s = _
  simp

@[simp] theorem run_seqRight [Monad m] (x : StateT σ m α) (y : StateT σ m β) (s : σ) : (x *> y).run s = (x.run s >>= fun p => y.run p.2) := by
  change (x >>= fun _ => y).run s = _
  simp

@[simp] theorem run_seqLeft {α β σ : Type u} [Monad m] (x : StateT σ m α) (y : StateT σ m β) (s : σ) : (x <* y).run s = (x.run s >>= fun p => y.run p.2 >>= fun p' => pure (p.1, p'.2)) := by
  change (x >>= fun a => y >>= fun _ => pure a).run s = _
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

/-! Note that the `MonadControl` instance for `StateT` is not monad-generic. -/

@[simp] theorem run_restoreM [Monad m] [LawfulMonad m] (x : stM m (StateT σ m) α) (s : σ) :
    StateT.run (restoreM x) s = pure x := by
  simp [restoreM, MonadControl.restoreM]
  rfl

@[simp] theorem run_liftWith [Monad m] [LawfulMonad m] (f : ({β : Type u} → StateT σ m β → m (stM m (StateT σ m) β)) → m α) (s : σ) :
    StateT.run (liftWith f) s = ((·, s) <$> f fun x => x.run s) := by
  simp [liftWith, MonadControl.liftWith, Function.comp_def]

@[simp] theorem run_controlAt [Monad m] [LawfulMonad m] (f : ({β : Type u} → StateT σ m β → m (stM m (StateT σ m) β)) → m (stM m (StateT σ m) α)) (s : σ) :
    StateT.run (controlAt m f) s = f fun x => x.run s := by
  simp [controlAt]

@[simp] theorem run_control [Monad m] [LawfulMonad m] (f : ({β : Type u} → StateT σ m β → m (stM m (StateT σ m) β)) → m (stM m (StateT σ m) α)) (s : σ) :
    StateT.run (control f) s = f fun x => x.run s := run_controlAt f s

end StateT

/-! # EStateM -/

namespace EStateM

@[simp, grind =] theorem run_pure (a : α) (s : σ) :
    EStateM.run (pure a : EStateM ε σ α) s = .ok a s := rfl

@[simp, grind =] theorem run_get (s : σ) :
    EStateM.run (get : EStateM ε σ σ) s = .ok s s := rfl

@[simp, grind =] theorem run_set (s₁ s₂ : σ) :
    EStateM.run (set s₁ : EStateM ε σ PUnit) s₂ = .ok .unit s₁ := rfl

@[simp, grind =] theorem run_modify (f : σ → σ) (s : σ) :
    EStateM.run (modify f : EStateM ε σ PUnit) s = .ok .unit (f s) := rfl

@[simp, grind =] theorem run_modifyGet (f : σ → α × σ) (s : σ) :
    EStateM.run (modifyGet f : EStateM ε σ α) s = .ok (f s).1 (f s).2 := rfl

@[simp, grind =] theorem run_throw (e : ε) (s : σ):
    EStateM.run (throw e : EStateM ε σ PUnit) s = .error e s := rfl

instance : LawfulMonad (EStateM ε σ) := .mk'
  (id_map := fun x => funext <| fun s => by
    dsimp only [EStateM.instMonad, EStateM.map]
    match x s with
    | .ok _ _ => rfl
    | .error _ _ => rfl)
  (pure_bind := fun _ _ => by rfl)
  (bind_assoc := fun x _ _ => funext <| fun s => by
    dsimp only [EStateM.instMonad, EStateM.bind]
    match x s with
    | .ok _ _ => rfl
    | .error _ _ => rfl)
  (map_const := fun _ _ => rfl)

end EStateM
