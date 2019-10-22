/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.State
import Init.Control.Except
universes u v

namespace EState

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

instance [HasToString ε] [HasToString α] : HasToString (Result ε σ α) := ⟨Result.toString⟩
instance [HasRepr ε] [HasRepr α] : HasRepr (Result ε σ α) := ⟨Result.repr⟩

end EState

def EState (ε σ α : Type u) := σ → EState.Result ε σ α

namespace EState

variables {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EState ε σ α) :=
⟨fun s => Result.error (default ε) s⟩

@[inline] protected def pure (a : α) : EState ε σ α :=
fun s => Result.ok a s

@[inline] protected def set (s : σ) : EState ε σ PUnit :=
fun _ => Result.ok ⟨⟩ s

@[inline] protected def get : EState ε σ σ :=
fun s => Result.ok s s

@[inline] protected def modifyGet (f : σ → α × σ) : EState ε σ α :=
fun s =>
  match f s with
  | (a, s) => Result.ok a s

@[inline] protected def throw (e : ε) : EState ε σ α :=
fun s => Result.error e s

@[inline] protected def catch (x : EState ε σ α) (handle : ε → EState ε σ α) : EState ε σ α :=
fun s =>
  match x s with
  | Result.error e s => handle e s
  | ok               => ok

@[inline] protected def orelse (x₁ x₂ : EState ε σ α) : EState ε σ α :=
fun s => match x₁ s with
  | Result.error _ s => x₂ s
  | ok               => ok

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] protected def orelse' (x₁ x₂ : EState ε σ α) (useFirstEx := true) : EState ε σ α :=
fun s => match x₁ s with
  | Result.error e₁ s₁ =>
    match x₂ s₁ with
    | Result.error e₂ s₂ => Result.error (if useFirstEx then e₁ else e₂) s₂
    | ok                 => ok
  | ok                 => ok

@[inline] def adaptExcept {ε' : Type u} [HasLift ε ε'] (x : EState ε σ α) : EState ε' σ α :=
fun s => match x s with
  | Result.error e s => Result.error (lift e) s
  | Result.ok a s    => Result.ok a s

@[inline] protected def bind (x : EState ε σ α) (f : α → EState ε σ β) : EState ε σ β :=
fun s => match x s with
  | Result.ok a s    => f a s
  | Result.error e s => Result.error e s

@[inline] protected def map (f : α → β) (x : EState ε σ α) : EState ε σ β :=
fun s => match x s with
  | Result.ok a s    => Result.ok (f a) s
  | Result.error e s => Result.error e s

@[inline] protected def seqRight (x : EState ε σ α) (y : EState ε σ β) : EState ε σ β :=
fun s => match x s with
  | Result.ok _ s    => y s
  | Result.error e s => Result.error e s

instance : Monad (EState ε σ) :=
{ bind := @EState.bind _ _, pure := @EState.pure _ _, map := @EState.map _ _, seqRight := @EState.seqRight _ _ }

instance : HasOrelse (EState ε σ α) :=
{ orelse := @EState.orelse _ _ _ }

instance : MonadState σ (EState ε σ) :=
{ set := @EState.set _ _, get := @EState.get _ _, modifyGet := @EState.modifyGet _ _ }

instance : MonadExcept ε (EState ε σ) :=
{ throw := @EState.throw _ _, catch := @EState.catch _ _ }

@[inline] def adaptState {σ₁ σ₂} (x : EState ε σ₁ α) (split : σ → σ₁ × σ₂) (merge : σ₁ → σ₂ → σ) : EState ε σ α :=
fun s =>
  let (s₁, s₂) := split s;
  match x s₁ with
  | Result.ok a s₁    => Result.ok a (merge s₁ s₂)
  | Result.error e s₁ => Result.error e (merge s₁ s₂)

@[inline] def fromState {ε σ α : Type} (x : State σ α) : EState ε σ α :=
fun s =>
  match x.run s with
  | (a, s') => EState.Result.ok a s'

@[inline] def run (x : EState ε σ α) (s : σ) : Result ε σ α :=
x s

@[inline] def run' (x : EState ε σ α) (s : σ) : Option α :=
match run x s with
| Result.ok v _    => some v
| Result.error _ _ => none

end EState
