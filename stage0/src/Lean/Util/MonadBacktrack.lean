/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

namespace Lean

/-- Similar to `MonadState`, but it retrieves/restores only the "backtrackable" part of the state -/
class MonadBacktrack (s : outParam Type) (m : Type → Type) where
  saveState    : m s
  restoreState : s → m Unit

export MonadBacktrack (saveState restoreState)

/--
Execute `x?`, but backtrack state if result is `none` or an exception was thrown.
-/
def commitWhenSome? [Monad m] [MonadBacktrack s m] [MonadExcept ε m] (x? : m (Option α)) : m (Option α) := do
  let s ← saveState
  try
    match (← x?) with
    | some a => return some a
    | none   =>
      restoreState s
      return none
  catch ex =>
    restoreState s
    throw ex

/--
Execute `x?`, but backtrack state if result is `none` or an exception was thrown.
If an exception is thrown, `none` is returned.
That is, this function is similar to `commitWhenSome?`, but swallows the exception and returns `none`.
-/
def commitWhenSomeNoEx? [Monad m] [MonadBacktrack s m] [MonadExcept ε m] (x? : m (Option α)) : m (Option α) :=
  try
    commitWhenSome? x?
  catch _ =>
    return none

def commitWhen [Monad m] [MonadBacktrack s m] [MonadExcept ε m] (x : m Bool) : m Bool := do
  let s ← saveState
  try
    match (← x) with
    | true  => pure true
    | false =>
      restoreState s
      pure false
  catch ex =>
    restoreState s
    throw ex

def commitIfNoEx [Monad m] [MonadBacktrack s m] [MonadExcept ε m] (x : m α) : m α := do
  let s ← saveState
  try
    x
  catch ex =>
    restoreState s
    throw ex

def withoutModifyingState [Monad m] [MonadFinally m] [MonadBacktrack s m] (x : m α) : m α := do
  let s ← saveState
  try
    x
  finally
    restoreState s

def observing? [Monad m] [MonadBacktrack s m] [MonadExcept ε m] (x : m α) : m (Option α) := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s
    return none

instance [MonadBacktrack s m] [Monad m] : MonadBacktrack s (ExceptT ε m) where
  saveState      := ExceptT.lift saveState
  restoreState s := ExceptT.lift <| restoreState s

end Lean
