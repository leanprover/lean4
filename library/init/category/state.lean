/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive
universes u v

def state (σ α : Type u) : Type u :=
σ → α × σ

section
variables {σ α β : Type u}

@[inline] def state_return (a : α) : state σ α :=
λ s, (a, s)

@[inline] def state_bind (a : state σ α) (b : α → state σ β) : state σ β :=
λ s, match (a s) with (a', s') := b a' s' end

instance (σ : Type u) : monad (state σ) :=
{pure := @state_return σ, bind := @state_bind σ,
 id_map := begin
   intros, apply funext, intro s,
   simp [state_bind], cases x s,
   apply rfl
 end,
 pure_bind := by intros; apply rfl,
 bind_assoc := begin
   intros, apply funext, intro s,
   simp [state_bind], cases x s,
   apply rfl
 end}
end

namespace state
@[inline] def read {σ : Type u} : state σ σ :=
λ s, (s, s)

@[inline] def write {σ : Type} : σ → state σ unit :=
λ s' s, ((), s')

@[inline] def write' {σ : Type u} : σ → state σ punit :=
λ s' s, (punit.star, s')
end state

def state_t (σ : Type u) (m : Type u → Type v) [monad m] (α : Type u) : Type (max u v) :=
σ → m (α × σ)

section
  variable  {σ : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}

  def state_t_return (a : α) : state_t σ m α :=
  λ s, show m (α × σ), from
    return (a, s)

  def state_t_bind (act₁ : state_t σ m α) (act₂ : α → state_t σ m β) : state_t σ m β :=
  λ s, show m (β × σ), from
     do (a, new_s) ← act₁ s,
        act₂ a new_s
end

instance (σ : Type u) (m : Type u → Type v) [monad m] : monad (state_t σ m) :=
{pure := @state_t_return σ m _, bind := @state_t_bind σ m _,
 id_map := begin
   intros, apply funext, intro,
   simp [state_t_bind, state_t_return, function.comp, return],
   assert h : state_t_bind._match_1 (λ (x : α) (s : σ), @pure m _ _ (x, s)) = pure,
   { apply funext, intro s, cases s, apply rfl },
   { rw h, apply @monad.bind_pure _ σ },
 end,
 pure_bind := begin
   intros, apply funext, intro,
   simp [state_t_bind, state_t_return, monad.pure_bind]
 end,
 bind_assoc := begin
   intros, apply funext, intro,
   simp [state_t_bind, state_t_return, monad.bind_assoc],
   apply congr_arg, apply funext, intro r,
   cases r, refl
 end}

section
  variable  {σ : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variable  [alternative m]
  variable  {α : Type u}

  def state_t_orelse (act₁ act₂ : state_t σ m α) : state_t σ m α :=
  λ s, act₁ s <|> act₂ s

  def state_t_failure : state_t σ m α :=
  λ s, failure
end

instance (σ : Type u) (m : Type u → Type v) [alternative m] [monad m] : alternative (state_t σ m) :=
{ state_t.monad σ m with
  failure := @state_t_failure σ m _ _,
  orelse  := @state_t_orelse σ m _ _ }

namespace state_t
def read {σ : Type u} {m : Type u → Type v} [monad m] : state_t σ m σ :=
λ s, return (s, s)

def write {σ : Type} {m : Type → Type v} [monad m] : σ → state_t σ m unit :=
λ s' s, return ((), s')

def write' {σ : Type u} {m : Type u → Type v} [monad m] : σ → state_t σ m punit :=
λ s' s, return (punit.star, s')

def modify {σ : Type} {m : Type → Type v} [monad m] (f : σ → σ) : state_t σ m unit :=
do s ← read, write (f s)

def modify' {σ : Type u} {m : Type u → Type v} [monad m] (f : σ → σ) : state_t σ m punit :=
do s ← read, write' (f s)

def lift {α σ : Type u} {m : Type u → Type v} [monad m] (t : m α) : state_t σ m α :=
λ s, do a ← t, return (a, s)
end state_t
