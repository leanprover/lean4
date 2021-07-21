/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The State monad transformer.
-/
prelude
import Init.Control.Basic
import Init.Control.Id
import Init.Control.Except
universe u v w

def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

@[inline] def StateT.run {σ : Type u} {m : Type u → Type v} {α : Type u} (x : StateT σ m α) (s : σ) : m (α × σ) :=
  x s

@[inline] def StateT.run' {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : StateT σ m α) (s : σ) : m α :=
  (·.1) <$> x s

@[reducible] def StateM (σ α : Type u) : Type u := StateT σ Id α

instance {σ α} [Subsingleton σ] [Subsingleton α] : Subsingleton (StateM σ α) where
  allEq x y := by
    apply funext
    intro s
    match x s, y s with
    | (a₁, s₁), (a₂, s₂) =>
      rw [Subsingleton.elim a₁ a₂, Subsingleton.elim s₁ s₂]

namespace StateT
section
variable {σ : Type u} {m : Type u → Type v} {α β : Type u}

@[inline] protected def map [Functor m] (f : α → β) (x : StateT σ m α) : StateT σ m β :=
  fun s => x s <&> fun (a, s) => (f a, s)

instance [Functor m] : Functor (StateT σ m) where
  map := StateT.map

@[inline] protected def pure [Pure m] (a : α) : StateT σ m α :=
  fun s => pure (a, s)

instance [Pure m] : Pure (StateT σ m) := ⟨StateT.pure⟩

@[inline] protected def bind [Bind m] (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
  fun s => do let (a, s) ← x s; f a s

instance [Bind m] : Bind (StateT σ m) := ⟨StateT.bind⟩

instance [Monad m] : Monad (StateT σ m) := {}

@[inline] protected def orElse [Alternative m] {α : Type u} (x₁ x₂ : StateT σ m α) : StateT σ m α :=
  fun s => x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] {α : Type u} : StateT σ m α :=
  fun s => failure

instance [Monad m] [Alternative m] : Alternative (StateT σ m) where
  failure := StateT.failure
  orElse  := StateT.orElse

@[inline] protected def get [Pure m] : StateT σ m σ :=
  fun s => pure (s, s)

@[inline] protected def set [Pure m] : σ → StateT σ m PUnit :=
  fun s' s => pure (⟨⟩, s')

@[inline] protected def modifyGet [Pure m] (f : σ → α × σ) : StateT σ m α :=
  fun s => pure (f s)

@[inline] protected def lift [Functor m] {α : Type u} (t : m α) : StateT σ m α :=
  fun s => t <&> fun a => (a, s)

instance [Functor m] : MonadLift m (StateT σ m) := ⟨StateT.lift⟩

instance (σ m) : MonadFunctor m (StateT σ m) := ⟨fun f x s => f (x s)⟩

instance (ε) [MonadExceptOf ε m] [Functor m] : MonadExceptOf ε (StateT σ m) := {
  throw    := StateT.lift ∘ throwThe ε
  tryCatch := fun x c s => tryCatchThe ε (x s) (fun e => c e s)
}

end
end StateT

section
variable {σ : Type u} {m : Type u → Type v}

instance [Pure m] : MonadStateOf σ (StateT σ m) where
  get       := StateT.get
  set       := StateT.set
  modifyGet := StateT.modifyGet

end

instance StateT.monadControl (σ : Type u) (m : Type u → Type v) [Monad m] : MonadControl m (StateT σ m) where
  stM      := fun α   => α × σ
  liftWith := fun f => do let s ← get; liftM (f (fun x => x.run s))
  restoreM := fun x => do let (a, s) ← liftM x; set s; pure a

instance StateT.tryFinally {m : Type u → Type v} {σ : Type u} [MonadFinally m] [Monad m] : MonadFinally (StateT σ m) where
  tryFinally' := fun x h s => do
    let ((a, _), (b, s'')) ← tryFinally' (x s) fun
      | some (a, s') => h (some a) s'
      | none         => h none s
    pure ((a, b), s'')
