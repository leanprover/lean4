/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

The combined Except and State Monad that minimizes the number
of memory allocations using the approach described in the paper
"Counting immutable beans" by Sebastian and Leo
-/
prelude
import init.control.state init.control.except
universes u v

namespace EState

inductive Result (ε σ α : Type u)
| ok    {} : α → σ → Result
| error {} : ε → σ → Result

variables {ε σ α : Type u}

inductive Result.IsOk : Result ε σ α → Prop
| mk (a : α) (s : σ) : Result.IsOk (Result.ok a s)

theorem notIsOkError {e : ε} {s : σ} (h : @Result.IsOk _ _ α (Result.error e s)) : False :=
match h with end

@[inline] def unreachableError {β : Type v} {e : ε} {s : σ} (h : @Result.IsOk _ _ α (Result.error e s)) : β :=
False.elim (notIsOkError h)

abbrev resultOk (ε σ α : Type u) := {r : Result ε σ α // r.IsOk}

@[inline] protected def resultOk.mk (a : α) (s : σ) : resultOk ε σ α :=
⟨Result.ok a s, Result.IsOk.mk a s⟩

protected def Result.toString [HasToString ε] [HasToString α] : Result ε σ α → String
| (Result.ok a _)    := "ok: " ++ toString a
| (Result.error e _) := "error: " ++ toString e

protected def Result.repr [HasRepr ε] [HasRepr α] : Result ε σ α → String
| (Result.error e _) := "(error " ++ repr e ++ ")"
| (Result.ok a _)    := "(ok " ++ repr a ++ ")"

instance [HasToString ε] [HasToString α] : HasToString (Result ε σ α) := ⟨Result.toString⟩
instance [HasRepr ε] [HasRepr α] : HasRepr (Result ε σ α) := ⟨Result.repr⟩

end EState

def EState (ε σ α : Type u) := EState.resultOk PUnit σ PUnit → EState.Result ε σ α

namespace EState

variables {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EState ε σ α) :=
⟨λ r, match r with
      | ⟨Result.ok _ s, _⟩    := Result.error (default ε) s
      | ⟨Result.error _ _, h⟩ := unreachableError h⟩

@[inline] protected def pure (a : α) : EState ε σ α :=
λ r, match r with
     | ⟨Result.ok _ s, _⟩    := Result.ok a s
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def put (s : σ) : EState ε σ PUnit :=
λ r, match r with
     | ⟨Result.ok _ _, _⟩    := Result.ok ⟨⟩ s
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def get : EState ε σ σ :=
λ r, match r with
     | ⟨Result.ok _ s, _⟩    := Result.ok s s
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def modify (f : σ → σ) : EState ε σ PUnit :=
λ r, match r with
     | ⟨Result.ok _ s, _⟩    := Result.ok ⟨⟩ (f s)
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def throw (e : ε) : EState ε σ α :=
λ r, match r with
     | ⟨Result.ok _ s, _⟩    := Result.error e s
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def catch (x : EState ε σ α) (handle : ε → EState ε σ α) : EState ε σ α :=
λ r, match x r with
     | Result.error e s := handle e (resultOk.mk ⟨⟩ s)
     | ok               := ok

@[inline] protected def orelse (x₁ x₂ : EState ε σ α) : EState ε σ α :=
λ r, match x₁ r with
     | Result.error _ s := x₂ (resultOk.mk ⟨⟩ s)
     | ok               := ok

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] protected def orelse' (x₁ x₂ : EState ε σ α) (useFirstEx := true) : EState ε σ α :=
λ r, match x₁ r with
     | Result.error e₁ s₁ :=
       (match x₂ (resultOk.mk ⟨⟩ s₁) with
        | Result.error e₂ s₂ := Result.error (if useFirstEx then e₁ else e₂) s₂
        | ok                 := ok)
     | ok                 := ok

@[inline] def adaptExcept {ε' : Type u} [HasLift ε ε'] (x : EState ε σ α) : EState ε' σ α :=
λ r, match x r with
     | Result.error e s := Result.error (lift e) s
     | Result.ok a s    := Result.ok a s

@[inline] protected def bind (x : EState ε σ α) (f : α → EState ε σ β) : EState ε σ β :=
λ r, match x r with
     | Result.ok a s    := f a (resultOk.mk ⟨⟩ s)
     | Result.error e s := Result.error e s

@[inline] protected def map (f : α → β) (x : EState ε σ α) : EState ε σ β :=
λ r, match x r with
     | Result.ok a s    := Result.ok (f a) s
     | Result.error e s := Result.error e s

instance : Monad (EState ε σ) :=
{ bind := @EState.bind _ _, pure := @EState.pure _ _, map := @EState.map _ _ }

instance : HasOrelse (EState ε σ) :=
{ orelse := @EState.orelse _ _ }

instance : MonadState σ (EState ε σ) :=
{ put := @EState.put _ _, get := @EState.get _ _, modify := @EState.modify _ _ }

instance : MonadExcept ε (EState ε σ) :=
{ throw := @EState.throw _ _, catch := @EState.catch _ _}

end EState
