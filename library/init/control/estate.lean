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

namespace Estate

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

end Estate

def Estate (ε σ α : Type u) := Estate.resultOk Punit σ Punit → Estate.Result ε σ α

namespace Estate

variables {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (Estate ε σ α) :=
⟨λ r, match r with
      | ⟨Result.ok _ s, _⟩    := Result.error (default ε) s
      | ⟨Result.error _ _, h⟩ := unreachableError h⟩

@[inline] protected def pure (a : α) : Estate ε σ α :=
λ r, match r with
     | ⟨Result.ok _ s, _⟩    := Result.ok a s
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def put (s : σ) : Estate ε σ Punit :=
λ r, match r with
     | ⟨Result.ok _ _, _⟩    := Result.ok ⟨⟩ s
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def get : Estate ε σ σ :=
λ r, match r with
     | ⟨Result.ok _ s, _⟩    := Result.ok s s
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def modify (f : σ → σ) : Estate ε σ Punit :=
λ r, match r with
     | ⟨Result.ok _ s, _⟩    := Result.ok ⟨⟩ (f s)
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def throw (e : ε) : Estate ε σ α :=
λ r, match r with
     | ⟨Result.ok _ s, _⟩    := Result.error e s
     | ⟨Result.error _ _, h⟩ := unreachableError h

@[inline] protected def catch (x : Estate ε σ α) (handle : ε → Estate ε σ α) : Estate ε σ α :=
λ r, match x r with
     | Result.error e s := handle e (resultOk.mk ⟨⟩ s)
     | ok               := ok

@[inline] protected def orelse (x₁ x₂ : Estate ε σ α) : Estate ε σ α :=
λ r, match x₁ r with
     | Result.error _ s := x₂ (resultOk.mk ⟨⟩ s)
     | ok               := ok

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] protected def orelse' (x₁ x₂ : Estate ε σ α) (useFirstEx := true) : Estate ε σ α :=
λ r, match x₁ r with
     | Result.error e₁ s₁ :=
       (match x₂ (resultOk.mk ⟨⟩ s₁) with
        | Result.error e₂ s₂ := Result.error (if useFirstEx then e₁ else e₂) s₂
        | ok                 := ok)
     | ok                 := ok

@[inline] def adaptExcept {ε' : Type u} [HasLift ε ε'] (x : Estate ε σ α) : Estate ε' σ α :=
λ r, match x r with
     | Result.error e s := Result.error (lift e) s
     | Result.ok a s    := Result.ok a s

@[inline] protected def bind (x : Estate ε σ α) (f : α → Estate ε σ β) : Estate ε σ β :=
λ r, match x r with
     | Result.ok a s    := f a (resultOk.mk ⟨⟩ s)
     | Result.error e s := Result.error e s

@[inline] protected def map (f : α → β) (x : Estate ε σ α) : Estate ε σ β :=
λ r, match x r with
     | Result.ok a s    := Result.ok (f a) s
     | Result.error e s := Result.error e s

instance : Monad (Estate ε σ) :=
{ bind := @Estate.bind _ _, pure := @Estate.pure _ _, map := @Estate.map _ _ }

instance : HasOrelse (Estate ε σ) :=
{ orelse := @Estate.orelse _ _ }

instance : MonadState σ (Estate ε σ) :=
{ put := @Estate.put _ _, get := @Estate.get _ _, modify := @Estate.modify _ _ }

instance : MonadExcept ε (Estate ε σ) :=
{ throw := @Estate.throw _ _, catch := @Estate.catch _ _}

end Estate
