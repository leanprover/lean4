/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.State
import Init.Control.Except
universes u v

namespace EStateM

inductive Result (ε σ α : Type u)
  | ok    : α → σ → Result ε σ α
  | error : ε → σ → Result ε σ α

variables {ε σ α : Type u}

instance [ToString ε] [ToString α] : ToString (Result ε σ α) := {
  toString := fun
    | Result.ok a _    => "ok: " ++ toString a
    | Result.error e _ => "error: " ++ toString e
}

instance [HasRepr ε] [HasRepr α] : HasRepr (Result ε σ α) := {
  repr := fun
    | Result.error e _ => "(error " ++ repr e ++ ")"
    | Result.ok a _    => "(ok " ++ repr a ++ ")"
}

instance [Inhabited ε] [Inhabited σ] : Inhabited (Result ε σ α) := ⟨Result.error (arbitrary _) (arbitrary _)⟩

end EStateM

open EStateM (Result) in
def EStateM (ε σ α : Type u) := σ → Result ε σ α

namespace EStateM

variables {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EStateM ε σ α) := ⟨fun s =>
  Result.error (arbitrary ε) s⟩

@[inline] protected def pure (a : α) : EStateM ε σ α := fun s =>
  Result.ok a s

@[inline] protected def set (s : σ) : EStateM ε σ PUnit := fun _ =>
  Result.ok ⟨⟩ s

@[inline] protected def get : EStateM ε σ σ := fun s =>
  Result.ok s s

@[inline] protected def modifyGet (f : σ → α × σ) : EStateM ε σ α := fun s =>
  match f s with
  | (a, s) => Result.ok a s

@[inline] protected def throw (e : ε) : EStateM ε σ α := fun s =>
  Result.error e s

/-- Auxiliary instance for saving/restoring the "backtrackable" part of the state. -/
class Backtrackable (δ : outParam $ Type u) (σ : Type u) :=
  (save    : σ → δ)
  (restore : σ → δ → σ)

@[inline] protected def tryCatch {δ} [Backtrackable δ σ] {α} (x : EStateM ε σ α) (handle : ε → EStateM ε σ α) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s
  match x s with
  | Result.error e s => handle e (Backtrackable.restore s d)
  | ok               => ok

@[inline] protected def orelse {δ} [Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error _ s => x₂ (Backtrackable.restore s d)
  | ok               => ok

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] protected def orelse' {δ} [Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) (useFirstEx := true) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error e₁ s₁ =>
    match x₂ (Backtrackable.restore s₁ d) with
    | Result.error e₂ s₂ => Result.error (if useFirstEx then e₁ else e₂) s₂
    | ok                 => ok
  | ok                 => ok

@[inline] def adaptExcept {ε' : Type u} (f : ε → ε') (x : EStateM ε σ α) : EStateM ε' σ α := fun s =>
  match x s with
  | Result.error e s => Result.error (f e) s
  | Result.ok a s    => Result.ok a s

@[inline] protected def bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => f a s
  | Result.error e s => Result.error e s

@[inline] protected def map (f : α → β) (x : EStateM ε σ α) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => Result.ok (f a) s
  | Result.error e s => Result.error e s

@[inline] protected def seqRight (x : EStateM ε σ PUnit) (y : EStateM ε σ β) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok _ s    => y s
  | Result.error e s => Result.error e s

instance : Monad (EStateM ε σ) := {
  bind     := EStateM.bind,
  pure     := EStateM.pure,
  map      := EStateM.map,
  seqRight := EStateM.seqRight
}

instance {δ} [Backtrackable δ σ] : HasOrelse (EStateM ε σ α) := {
  orelse := EStateM.orelse
}

instance : MonadStateOf σ (EStateM ε σ) := {
  set       := EStateM.set,
  get       := EStateM.get,
  modifyGet := EStateM.modifyGet
}

instance {δ} [Backtrackable δ σ] : MonadExceptOf ε (EStateM ε σ) := {
  throw    := EStateM.throw,
  tryCatch := EStateM.tryCatch
}

instance : MonadFinally (EStateM ε σ) := {
  tryFinally' := fun x h s =>
    let r := x s
    match r with
    | Result.ok a s    => match h (some a) s with
      | Result.ok b s    => Result.ok (a, b) s
      | Result.error e s => Result.error e s
    | Result.error e₁ s => match h none s with
      | Result.ok _ s     => Result.error e₁ s
      | Result.error e₂ s => Result.error e₂ s
}

@[inline] def fromStateM {ε σ α : Type} (x : StateM σ α) : EStateM ε σ α := fun s =>
  match x.run s with
  | (a, s') => EStateM.Result.ok a s'

@[inline] def run (x : EStateM ε σ α) (s : σ) : Result ε σ α :=
  x s

@[inline] def run' (x : EStateM ε σ α) (s : σ) : Option α :=
  match run x s with
  | Result.ok v _    => some v
  | Result.error _ _ => none

@[inline] def dummySave : σ → PUnit := fun _ => ⟨⟩

@[inline] def dummyRestore : σ → PUnit → σ := fun s _ => s

/- Dummy default instance -/
instance nonBacktrackable : Backtrackable PUnit σ := {
  save    := dummySave,
  restore := dummyRestore
}

end EStateM
