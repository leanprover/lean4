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
| ok    {} : α → σ → Result
| error {} : ε → σ → Result

variables {ε σ α : Type u}

protected def Result.toString [HasToString ε] [HasToString α] : Result ε σ α → String
| Result.ok a _    => "ok: " ++ toString a
| Result.error e _ => "error: " ++ toString e

protected def Result.repr [HasRepr ε] [HasRepr α] : Result ε σ α → String
| Result.error e _ => "(error " ++ repr e ++ ")"
| Result.ok a _    => "(ok " ++ repr a ++ ")"

instance Result.hasToString [HasToString ε] [HasToString α] : HasToString (Result ε σ α) := ⟨Result.toString⟩
instance Result.hasRepr [HasRepr ε] [HasRepr α] : HasRepr (Result ε σ α) := ⟨Result.repr⟩
instance Result.inhabited [Inhabited ε] [Inhabited σ] : Inhabited (Result ε σ α) := ⟨Result.error (arbitrary _) (arbitrary _)⟩

end EStateM

def EStateM (ε σ α : Type u) := σ → EStateM.Result ε σ α

namespace EStateM

variables {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EStateM ε σ α) :=
⟨fun s => Result.error (arbitrary ε) s⟩

@[inline] protected def pure (a : α) : EStateM ε σ α :=
fun s => Result.ok a s

@[inline] protected def set (s : σ) : EStateM ε σ PUnit :=
fun _ => Result.ok ⟨⟩ s

@[inline] protected def get : EStateM ε σ σ :=
fun s => Result.ok s s

@[inline] protected def modifyGet (f : σ → α × σ) : EStateM ε σ α :=
fun s =>
  match f s with
  | (a, s) => Result.ok a s

@[inline] protected def throw (e : ε) : EStateM ε σ α :=
fun s => Result.error e s

/-- Auxiliary instance for saving/restoring the "backtrackable" part of the state. -/
class Backtrackable (δ : outParam $ Type u) (σ : Type u) :=
(save    : σ → δ)
(restore : σ → δ → σ)

@[inline] protected def catch {δ} [Backtrackable δ σ] {α} (x : EStateM ε σ α) (handle : ε → EStateM ε σ α) : EStateM ε σ α :=
fun s =>
  let d := Backtrackable.save s;
  match x s with
  | Result.error e s => handle e (Backtrackable.restore s d)
  | ok               => ok

@[inline] protected def orelse {δ} [Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) : EStateM ε σ α :=
fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error _ s => x₂ (Backtrackable.restore s d)
  | ok               => ok

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] protected def orelse' {δ} [Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) (useFirstEx := true) : EStateM ε σ α :=
fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error e₁ s₁ =>
    match x₂ (Backtrackable.restore s₁ d) with
    | Result.error e₂ s₂ => Result.error (if useFirstEx then e₁ else e₂) s₂
    | ok                 => ok
  | ok                 => ok

@[inline] def adaptExcept {ε' : Type u} [HasLift ε ε'] (x : EStateM ε σ α) : EStateM ε' σ α :=
fun s => match x s with
  | Result.error e s => Result.error (lift e) s
  | Result.ok a s    => Result.ok a s

@[inline] protected def bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) : EStateM ε σ β :=
fun s => match x s with
  | Result.ok a s    => f a s
  | Result.error e s => Result.error e s

@[inline] protected def map (f : α → β) (x : EStateM ε σ α) : EStateM ε σ β :=
fun s => match x s with
  | Result.ok a s    => Result.ok (f a) s
  | Result.error e s => Result.error e s

@[inline] protected def seqRight (x : EStateM ε σ α) (y : EStateM ε σ β) : EStateM ε σ β :=
fun s => match x s with
  | Result.ok _ s    => y s
  | Result.error e s => Result.error e s

instance : Monad (EStateM ε σ) :=
{ bind := @EStateM.bind _ _, pure := @EStateM.pure _ _, map := @EStateM.map _ _, seqRight := @EStateM.seqRight _ _ }

instance {δ} [Backtrackable δ σ] : HasOrelse (EStateM ε σ α) :=
{ orelse := @EStateM.orelse _ _ _ _ _ }

instance : MonadState σ (EStateM ε σ) :=
{ set := @EStateM.set _ _, get := @EStateM.get _ _, modifyGet := @EStateM.modifyGet _ _ }

instance {δ} [Backtrackable δ σ] : MonadExcept ε (EStateM ε σ) :=
{ throw := @EStateM.throw _ _, catch := @EStateM.catch _ _ _ _ }

@[inline] def adaptState {σ₁ σ₂} (split : σ → σ₁ × σ₂) (merge : σ₁ → σ₂ → σ) (x : EStateM ε σ₁ α) : EStateM ε σ α :=
fun s =>
  let (s₁, s₂) := split s;
  match x s₁ with
  | Result.ok a s₁    => Result.ok a (merge s₁ s₂)
  | Result.error e s₁ => Result.error e (merge s₁ s₂)

instance {ε σ σ'} : MonadStateAdapter σ σ' (EStateM ε σ) (EStateM ε σ') :=
⟨fun σ'' α => EStateM.adaptState⟩

@[inline] def fromStateM {ε σ α : Type} (x : StateM σ α) : EStateM ε σ α :=
fun s =>
  match x.run s with
  | (a, s') => EStateM.Result.ok a s'

@[inline] def run (x : EStateM ε σ α) (s : σ) : Result ε σ α :=
x s

@[inline] def run' (x : EStateM ε σ α) (s : σ) : Option α :=
match run x s with
| Result.ok v _    => some v
| Result.error _ _ => none

@[inline] def dummySave : σ → PUnit :=
fun _ => ⟨⟩

@[inline] def dummyRestore : σ → PUnit → σ :=
fun s _ => s

/- Dummy default instance -/
instance nonBacktrackable : Backtrackable PUnit σ :=
{ save    := dummySave,
  restore := dummyRestore }

end EStateM
