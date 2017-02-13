/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.category.monad init.category.alternative

def state (σ : Type) (α : Type) : Type :=
σ → α × σ

section
variables {σ : Type} {α β : Type}

@[inline] def state_fmap (f : α → β) (a : state σ α) : state σ β :=
λ s, match (a s) with (a', s') := (f a', s') end

@[inline] def state_return (a : α) : state σ α :=
λ s, (a, s)

@[inline] def state_bind (a : state σ α) (b : α → state σ β) : state σ β :=
λ s, match (a s) with (a', s') := b a' s' end

instance (σ : Type) : monad (state σ) :=
{ map := @state_fmap σ,
  ret  := @state_return σ,
  bind := @state_bind σ }
end

namespace state
@[inline] def read {σ : Type} : state σ σ :=
λ s, (s, s)

@[inline] def write {σ : Type} : σ → state σ unit :=
λ s' s, ((), s')
end state

def state_t (σ : Type) (m : Type → Type) [monad m] (α : Type) : Type :=
σ → m (α × σ)

section
  variable  {σ : Type}
  variable  {m : Type → Type}
  variable  [monad m]
  variables {α β : Type}

  def state_t_fmap (f : α → β) (act : state_t σ m α) : state_t σ m β :=
  λ s, show m (β × σ), from
    do (a, new_s) ← act s,
       return (f a, new_s)

  def state_t_return (a : α) : state_t σ m α :=
  λ s, show m (α × σ), from
    return (a, s)

  def state_t_bind (act₁ : state_t σ m α) (act₂ : α → state_t σ m β) : state_t σ m β :=
  λ s, show m (β × σ), from
     do (a, new_s) ← act₁ s,
        act₂ a new_s
end

instance (σ : Type) (m : Type → Type) [monad m] : monad (state_t σ m) :=
{ map  := @state_t_fmap σ m _,
  ret  := @state_t_return σ m _,
  bind := @state_t_bind σ m _}

section
  variable  {σ : Type}
  variable  {m : Type → Type}
  variable  [monad m]
  variable  [alternative m]
  variable  {α : Type}

  def state_t_orelse (act₁ act₂ : state_t σ m α) : state_t σ m α :=
  λ s, act₁ s <|> act₂ s

  def state_t_failure : state_t σ m α :=
  λ s, failure
end

instance (σ : Type) (m : Type → Type) [alternative m] [monad m] : alternative (state_t σ m) :=
{ map     := @state_t_fmap σ m _,
  pure    := @state_t_return σ m _,
  seq     := @fapp _ _,
  failure := @state_t_failure σ m _ _,
  orelse  := @state_t_orelse σ m _ _ }

namespace state_t
def read {σ : Type} {m : Type → Type} [monad m] : state_t σ m σ :=
λ s, return (s, s)

def write {σ : Type} {m : Type → Type} [monad m] : σ → state_t σ m unit :=
λ s' s, return ((), s')

def modify {σ : Type} {m : Type → Type} [monad m] (f : σ → σ) : state_t σ m unit :=
do s ← read, write (f s)

def lift {α σ : Type} {m : Type → Type} [monad m] (t : m α) : state_t σ m α :=
λ s, do a ← t, return (a, s)
end state_t
