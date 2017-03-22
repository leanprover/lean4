/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive

universes u v

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
{pure := @option_t_return m _, bind := @option_t_bind m _,
 id_map := begin
   intros,
   dsimp [option_t_bind],
   assert h : option_t_bind._match_1 option_t_return = @pure m _ (option α),
   { apply funext, intro s, cases s, apply rfl, apply rfl },
   { rw h, apply @monad.bind_pure _ (option α) m },
 end,
 pure_bind := begin
   intros,
   dsimp [option_t_bind, option_t_return],
   dsimp [return, pure, bind], -- TODO: fix signature of `pure_bind`
   rw [monad.pure_bind], apply rfl
 end,
 bind_assoc := begin
   intros,
   dsimp [option_t_bind, option_t_return, bind],
   rw [monad.bind_assoc],
   apply congr_arg, apply funext, intro x,
   cases x,
   { dsimp [option_t_bind._match_1, return, pure],
     rw [monad.pure_bind], apply rfl },
   { apply rfl }
 end}

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
{ @option_t.monad m _ with
  failure := @option_t_fail m _,
  orelse  := @option_t_orelse m _ }

def option_t.lift {m : Type u → Type v} [monad m] {α : Type u} (a : m α) : option_t m α :=
(some <$> a : m (option α))
