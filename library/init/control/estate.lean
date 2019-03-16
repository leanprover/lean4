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

inductive result.is_ok : result ε σ α → Prop
| mk (a : α) (s : σ) : result.is_ok (result.ok a s)

theorem not_is_ok_error {e : ε} {s : σ} (h : @result.is_ok _ _ α (result.error e s)) : false :=
match h with end

@[inline] def unreachable_error {β : Type v} {e : ε} {s : σ} (h : @result.is_ok _ _ α (result.error e s)) : β :=
false.elim (not_is_ok_error h)

abbrev result_ok (ε σ α : Type u) := {r : result ε σ α // r.is_ok}

@[inline] protected def result_ok.mk (a : α) (s : σ) : result_ok ε σ α :=
⟨result.ok a s, result.is_ok.mk a s⟩

protected def result.to_string [has_to_string ε] [has_to_string α] : result ε σ α → string
| (result.ok a _)    := "ok: " ++ to_string a
| (result.error e _) := "error: " ++ to_string e

protected def result.repr [has_repr ε] [has_repr α] : result ε σ α → string
| (result.error e _) := "(error " ++ repr e ++ ")"
| (result.ok a _)    := "(ok " ++ repr a ++ ")"

instance [has_to_string ε] [has_to_string α] : has_to_string (result ε σ α) := ⟨result.to_string⟩
instance [has_repr ε] [has_repr α] : has_repr (result ε σ α) := ⟨result.repr⟩

end estate

def estate (ε σ α : Type u) := estate.result_ok punit σ punit → estate.result ε σ α

namespace estate

variables {ε σ α β : Type u}

@[inline] protected def pure (a : α) : estate ε σ α :=
λ r, match r with
     | ⟨result.ok _ s, _⟩    := result.ok a s
     | ⟨result.error _ _, h⟩ := unreachable_error h

@[inline] protected def put (s : σ) : estate ε σ punit :=
λ r, match r with
     | ⟨result.ok _ _, _⟩    := result.ok ⟨⟩ s
     | ⟨result.error _ _, h⟩ := unreachable_error h

@[inline] protected def get : estate ε σ σ :=
λ r, match r with
     | ⟨result.ok _ s, _⟩    := result.ok s s
     | ⟨result.error _ _, h⟩ := unreachable_error h

@[inline] protected def modify (f : σ → σ) : estate ε σ punit :=
λ r, match r with
     | ⟨result.ok _ s, _⟩    := result.ok ⟨⟩ (f s)
     | ⟨result.error _ _, h⟩ := unreachable_error h

@[inline] protected def throw (e : ε) : estate ε σ α :=
λ r, match r with
     | ⟨result.ok _ s, _⟩    := result.error e s
     | ⟨result.error _ _, h⟩ := unreachable_error h

@[inline] protected def catch (x : estate ε σ α) (handle : ε → estate ε σ α) : estate ε σ α :=
λ r, match x r with
     | result.error e s := handle e (result_ok.mk ⟨⟩ s)
     | ok               := ok

@[inline] protected def orelse (x₁ x₂ : estate ε σ α) : estate ε σ α :=
λ r, match x₁ r with
     | result.error _ s := x₂ (result_ok.mk ⟨⟩ s)
     | ok               := ok

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
@[inline] protected def orelse' (x₁ x₂ : estate ε σ α) (use_first_ex := tt) : estate ε σ α :=
λ r, match x₁ r with
     | result.error e₁ s₁ :=
       (match x₂ (result_ok.mk ⟨⟩ s₁) with
        | result.error e₂ s₂ := result.error (if use_first_ex then e₁ else e₂) s₂
        | ok                 := ok)
     | ok                 := ok

@[inline] def adapt_except {ε' : Type u} [has_lift_t ε' ε] (f : ε → ε') (x : estate ε σ α) : estate ε' σ α :=
λ r, match x r with
     | result.error e s := result.error (f e) s
     | result.ok a s    := result.ok a s

@[inline] protected def bind (x : estate ε σ α) (f : α → estate ε σ β) : estate ε σ β :=
λ r, match x r with
     | result.ok a s    := f a (result_ok.mk ⟨⟩ s)
     | result.error e s := result.error e s

@[inline] protected def map (f : α → β) (x : estate ε σ α) : estate ε σ β :=
λ r, match x r with
     | result.ok a s    := result.ok (f a) s
     | result.error e s := result.error e s

instance : monad (estate ε σ) :=
{ bind := @estate.bind _ _, pure := @estate.pure _ _, map := @estate.map _ _ }

instance : has_orelse (estate ε σ) :=
{ orelse := @estate.orelse _ _ }

instance : monad_state σ (estate ε σ) :=
{ put := @estate.put _ _, get := @estate.get _ _, modify := @estate.modify _ _ }

instance : monad_except ε (estate ε σ) :=
{ throw := @estate.throw _ _, catch := @estate.catch _ _}

end estate
