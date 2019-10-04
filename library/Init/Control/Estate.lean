/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

The combined Except and State Monad that minimizes the number
of memory allocations using the approach described in the paper
"Counting immutable beans" by Sebastian and Leo
-/
prelude
import init.control.state
import init.control.except
universes u v

namespace EState

inductive Result (ε σ α : Type u)
| ok    {} : α → σ → Result
| error {} : ε → σ → Result

variables {ε σ α : Type u}

inductive Result.IsOk : Result ε σ α → Prop
| mk (a : α) (s : σ) : Result.IsOk (Result.ok a s)

theorem notIsOkError {e : ε} {s : σ} (h : @Result.IsOk _ _ α (Result.error e s)) : False :=
nomatch h

@[inline] def unreachableError {β : Type v} {e : ε} {s : σ} (h : @Result.IsOk _ _ α (Result.error e s)) : β :=
False.elim (notIsOkError h)

abbrev resultOk (ε σ α : Type u) := {r : Result ε σ α // r.IsOk}

@[inline] protected def resultOk.mk (a : α) (s : σ) : resultOk ε σ α :=
⟨Result.ok a s, Result.IsOk.mk a s⟩

protected def Result.toString [HasToString ε] [HasToString α] : Result ε σ α → String
| Result.ok a _    => "ok: " ++ toString a
| Result.error e _ => "error: " ++ toString e

protected def Result.repr [HasRepr ε] [HasRepr α] : Result ε σ α → String
| Result.error e _ => "(error " ++ repr e ++ ")"
| Result.ok a _    => "(ok " ++ repr a ++ ")"

instance [HasToString ε] [HasToString α] : HasToString (Result ε σ α) := ⟨Result.toString⟩
instance [HasRepr ε] [HasRepr α] : HasRepr (Result ε σ α) := ⟨Result.repr⟩

end EState

def EState (ε σ α : Type u) := EState.resultOk PUnit σ PUnit → EState.Result ε σ α

namespace EState

variables {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EState ε σ α) :=
⟨fun r => match r with
  | ⟨Result.ok _ s, _⟩    => Result.error (default ε) s
  | ⟨Result.error _ _, h⟩ => unreachableError h⟩

@[inline] protected def pure (a : α) : EState ε σ α :=
fun r => match r with
  | ⟨Result.ok _ s, _⟩    => Result.ok a s
  | ⟨Result.error _ _, h⟩ => unreachableError h

@[inline] protected def set (s : σ) : EState ε σ PUnit :=
fun r => match r with
  | ⟨Result.ok _ _, _⟩    => Result.ok ⟨⟩ s
  | ⟨Result.error _ _, h⟩ => unreachableError h

@[inline] protected def get : EState ε σ σ :=
fun r => match r with
  | ⟨Result.ok _ s, _⟩    => Result.ok s s
  | ⟨Result.error _ _, h⟩ => unreachableError h

@[inline] protected def modifyGet (f : σ → α × σ) : EState ε σ α :=
fun r => match r with
  | ⟨Result.ok _ s, _⟩    =>
    match f s with
    | (a, s) => Result.ok a s
  | ⟨Result.error _ _, h⟩ => unreachableError h

@[inline] protected def throw (e : ε) : EState ε σ α :=
fun r => match r with
  | ⟨Result.ok _ s, _⟩    => Result.error e s
  | ⟨Result.error _ _, h⟩ => unreachableError h

@[inline] protected def catch (x : EState ε σ α) (handle : ε → EState ε σ α) : EState ε σ α :=
fun r => match x r with
  | Result.error e s => handle e (resultOk.mk ⟨⟩ s)
  | ok               => ok

@[inline] protected def orelse (x₁ x₂ : EState ε σ α) : EState ε σ α :=
fun r => match x₁ r with
  | Result.error _ s => x₂ (resultOk.mk ⟨⟩ s)
  | ok               => ok

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] protected def orelse' (x₁ x₂ : EState ε σ α) (useFirstEx := true) : EState ε σ α :=
fun r => match x₁ r with
  | Result.error e₁ s₁ =>
    match x₂ (resultOk.mk ⟨⟩ s₁) with
    | Result.error e₂ s₂ => Result.error (if useFirstEx then e₁ else e₂) s₂
    | ok                 => ok
  | ok                 => ok

@[inline] def adaptExcept {ε' : Type u} [HasLift ε ε'] (x : EState ε σ α) : EState ε' σ α :=
fun r => match x r with
  | Result.error e s => Result.error (lift e) s
  | Result.ok a s    => Result.ok a s

@[inline] protected def bind (x : EState ε σ α) (f : α → EState ε σ β) : EState ε σ β :=
fun r => match x r with
  | Result.ok a s    => f a (resultOk.mk ⟨⟩ s)
  | Result.error e s => Result.error e s

@[inline] protected def map (f : α → β) (x : EState ε σ α) : EState ε σ β :=
fun r => match x r with
  | Result.ok a s    => Result.ok (f a) s
  | Result.error e s => Result.error e s

@[inline] protected def seqRight (x : EState ε σ α) (y : EState ε σ β) : EState ε σ β :=
fun r => match x r with
  | Result.ok _ s    => y (resultOk.mk ⟨⟩ s)
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
fun r => match r with
  | ⟨Result.error _ _, h⟩ => unreachableError h
  | ⟨Result.ok _ s, _⟩    =>
    let (s₁, s₂) := split s;
    match x (resultOk.mk ⟨⟩ s₁) with
    | Result.ok a s₁    => Result.ok a (merge s₁ s₂)
    | Result.error e s₁ => Result.error e (merge s₁ s₂)

def fromState {ε σ α : Type} (s : State σ α) : EState ε σ α :=
λ (ok : EState.resultOk PUnit σ PUnit) =>
  match ok with
  | ⟨EState.Result.ok _ st₁, _⟩ =>
    match s.run st₁ with
    | ⟨val₂, st₂⟩ => EState.Result.ok val₂ st₂
  | ⟨EState.Result.error _ _, H⟩ => False.elim $ EState.notIsOkError H

@[inline] def run (x : EState ε σ α) (s : σ) : Result ε σ α :=
x (resultOk.mk ⟨⟩ s)

@[inline] def run' (x : EState ε σ α) (s : σ) : Option α :=
match run x s with
| Result.ok v _    => some v
| Result.error _ _ => none

end EState
