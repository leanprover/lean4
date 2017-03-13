/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import .basic

universes u v

@[inline] def option_bind {α : Type u} {β : Type v} : option α → (α → option β) → option β
| none     b := none
| (some a) b := b a

instance : monad option :=
{pure := @some, bind := @option_bind}

def option_orelse {α : Type u} : option α → option α → option α
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

instance : alternative option :=
{ option.monad with
  failure := @none,
  orelse  := @option_orelse }

def option_t (m : Type u → Type v) [monad m] (α : Type u) : Type v :=
m (option α)

@[inline] def option_t_bind {m : Type u → Type v} [monad m] {α β : Type u} (a : option_t m α) (b : α → option_t m β)
                               : option_t m β :=
show m (option β), from
do o ← a,
   match o with
   | none     := return none
   | (some a) := b a
   end

@[inline] def option_t_return {m : Type u → Type v} [monad m] {α : Type u} (a : α) : option_t m α :=
show m (option α), from
return (some a)

instance {m : Type u → Type v} [monad m] : monad (option_t m) :=
{pure := @option_t_return m _, bind := @option_t_bind m _}

def option_t_orelse {m : Type u → Type v} [monad m] {α : Type u} (a : option_t m α) (b : option_t m α) : option_t m α :=
show m (option α), from
do o ← a,
   match o with
   | none     := b
   | (some v) := return (some v)
   end

def option_t_fail {m : Type u → Type v} [monad m] {α : Type u} : option_t m α :=
show m (option α), from
return none

instance {m : Type u → Type v} [monad m] : alternative (option_t m) :=
{ option_t.monad with
  failure := @option_t_fail m _,
  orelse  := @option_t_orelse m _ }

def option_t.lift {m : Type u → Type v} [monad m] {α : Type u} (a : m α) : option_t m α :=
(some <$> a : m (option α))
