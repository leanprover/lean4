/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

The combined except and state monad that minimizes the number
of memory allocations using the approach described in the paper
"Counting immutable beans" by Sebastian and Leo
-/
prelude
import init.control.state init.control.except
universes u v

namespace estate

inductive result (ε σ α : Type u)
| ok    {} : α → σ → result
| error {} : ε → σ → result

variables {ε σ α : Type u}

inductive result.isOk : result ε σ α → Prop
| mk (a : α) (s : σ) : result.isOk (result.ok a s)

theorem notIsOkError {e : ε} {s : σ} (h : @result.isOk _ _ α (result.error e s)) : false :=
match h with end

@[inline] def unreachableError {β : Type v} {e : ε} {s : σ} (h : @result.isOk _ _ α (result.error e s)) : β :=
false.elim (notIsOkError h)

abbrev resultOk (ε σ α : Type u) := {r : result ε σ α // r.isOk}

@[inline] protected def resultOk.mk (a : α) (s : σ) : resultOk ε σ α :=
⟨result.ok a s, result.isOk.mk a s⟩

protected def result.toString [hasToString ε] [hasToString α] : result ε σ α → string
| (result.ok a _)    := "ok: " ++ toString a
| (result.error e _) := "error: " ++ toString e

protected def result.repr [hasRepr ε] [hasRepr α] : result ε σ α → string
| (result.error e _) := "(error " ++ repr e ++ ")"
| (result.ok a _)    := "(ok " ++ repr a ++ ")"

instance [hasToString ε] [hasToString α] : hasToString (result ε σ α) := ⟨result.toString⟩
instance [hasRepr ε] [hasRepr α] : hasRepr (result ε σ α) := ⟨result.repr⟩

end estate

def estate (ε σ α : Type u) := estate.resultOk punit σ punit → estate.result ε σ α

namespace estate

variables {ε σ α β : Type u}

instance [inhabited ε] : inhabited (estate ε σ α) :=
⟨λ r, match r with
      | ⟨result.ok _ s, _⟩    := result.error (default ε) s
      | ⟨result.error _ _, h⟩ := unreachableError h⟩

@[inline] protected def pure (a : α) : estate ε σ α :=
λ r, match r with
     | ⟨result.ok _ s, _⟩    := result.ok a s
     | ⟨result.error _ _, h⟩ := unreachableError h

@[inline] protected def put (s : σ) : estate ε σ punit :=
λ r, match r with
     | ⟨result.ok _ _, _⟩    := result.ok ⟨⟩ s
     | ⟨result.error _ _, h⟩ := unreachableError h

@[inline] protected def get : estate ε σ σ :=
λ r, match r with
     | ⟨result.ok _ s, _⟩    := result.ok s s
     | ⟨result.error _ _, h⟩ := unreachableError h

@[inline] protected def modify (f : σ → σ) : estate ε σ punit :=
λ r, match r with
     | ⟨result.ok _ s, _⟩    := result.ok ⟨⟩ (f s)
     | ⟨result.error _ _, h⟩ := unreachableError h

@[inline] protected def throw (e : ε) : estate ε σ α :=
λ r, match r with
     | ⟨result.ok _ s, _⟩    := result.error e s
     | ⟨result.error _ _, h⟩ := unreachableError h

@[inline] protected def catch (x : estate ε σ α) (handle : ε → estate ε σ α) : estate ε σ α :=
λ r, match x r with
     | result.error e s := handle e (resultOk.mk ⟨⟩ s)
     | ok               := ok

@[inline] protected def orelse (x₁ x₂ : estate ε σ α) : estate ε σ α :=
λ r, match x₁ r with
     | result.error _ s := x₂ (resultOk.mk ⟨⟩ s)
     | ok               := ok

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] protected def orelse' (x₁ x₂ : estate ε σ α) (useFirstEx := tt) : estate ε σ α :=
λ r, match x₁ r with
     | result.error e₁ s₁ :=
       (match x₂ (resultOk.mk ⟨⟩ s₁) with
        | result.error e₂ s₂ := result.error (if useFirstEx then e₁ else e₂) s₂
        | ok                 := ok)
     | ok                 := ok

@[inline] def adaptExcept {ε' : Type u} [hasLift ε ε'] (x : estate ε σ α) : estate ε' σ α :=
λ r, match x r with
     | result.error e s := result.error (lift e) s
     | result.ok a s    := result.ok a s

@[inline] protected def bind (x : estate ε σ α) (f : α → estate ε σ β) : estate ε σ β :=
λ r, match x r with
     | result.ok a s    := f a (resultOk.mk ⟨⟩ s)
     | result.error e s := result.error e s

@[inline] protected def map (f : α → β) (x : estate ε σ α) : estate ε σ β :=
λ r, match x r with
     | result.ok a s    := result.ok (f a) s
     | result.error e s := result.error e s

instance : monad (estate ε σ) :=
{ bind := @estate.bind _ _, pure := @estate.pure _ _, map := @estate.map _ _ }

instance : hasOrelse (estate ε σ) :=
{ orelse := @estate.orelse _ _ }

instance : monadState σ (estate ε σ) :=
{ put := @estate.put _ _, get := @estate.get _ _, modify := @estate.modify _ _ }

instance : monadExcept ε (estate ε σ) :=
{ throw := @estate.throw _ _, catch := @estate.catch _ _}

end estate
