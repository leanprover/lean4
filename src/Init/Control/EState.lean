/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.State
import Init.Control.Except
import Init.Data.ToString.Basic
universe u v

namespace EStateM

variable {ε σ α : Type u}

instance [ToString ε] [ToString α] : ToString (Result ε σ α) where
  toString
    | Result.ok a _    => "ok: " ++ toString a
    | Result.error e _ => "error: " ++ toString e

instance [Repr ε] [Repr α] : Repr (Result ε σ α) where
  reprPrec
    | Result.error e _, prec => Repr.addAppParen ("EStateM.Result.error " ++ reprArg e) prec
    | Result.ok a _, prec    => Repr.addAppParen ("EStateM.Result.ok " ++ reprArg a) prec

end EStateM

namespace EStateM

variable {ε σ α β : Type u}

/--
Alternative orElse operator that allows callers to select which exception should be used when both
operations fail. The default is to use the first exception since the standard `orElse` uses the
second.
-/
@[always_inline, inline]
protected def orElse' {δ} [Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) (useFirstEx := true) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error e₁ s₁ =>
    match x₂ (Backtrackable.restore s₁ d) with
    | Result.error e₂ s₂ => Result.error (if useFirstEx then e₁ else e₂) s₂
    | ok                 => ok
  | ok                 => ok

@[always_inline]
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

/--
Converts a state monad action into a state monad action with exceptions.

The resulting action does not throw an exception.
-/
@[always_inline, inline] def fromStateM {ε σ α : Type} (x : StateM σ α) : EStateM ε σ α := fun s =>
  match x.run s with
  | (a, s') => EStateM.Result.ok a s'

end EStateM
