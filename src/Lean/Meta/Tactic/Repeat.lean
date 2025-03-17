/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Lean.Meta.Basic

namespace Lean.Meta
/--
Implementation of `repeat'` and `repeat1'`.

`repeat'Core f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.

Returns a boolean indicating whether `f` succeeded at least once, and
all the remaining goals (i.e. those on which `f` failed).
-/
def repeat'Core [Monad m] [MonadExcept ε m] [MonadBacktrack s m] [MonadMCtx m]
    (f : MVarId → m (List MVarId)) (goals : List MVarId) (maxIters := 100000) :
    m (Bool × List MVarId) := do
  let (progress, acc) ← go maxIters false goals [] #[]
  pure (progress, (← acc.filterM fun g => not <$> g.isAssigned).toList)
where
  /-- Auxiliary for `repeat'Core`. `repeat'Core.go f maxIters progress goals stk acc` evaluates to
  essentially `acc.toList ++ repeat' f (goals::stk).join maxIters`: that is, `acc` are goals we will
  not revisit, and `(goals::stk).join` is the accumulated todo list of subgoals. -/
  go : Nat → Bool → List MVarId → List (List MVarId) → Array MVarId → m (Bool × Array MVarId)
  | _, p, [], [], acc => pure (p, acc)
  | n, p, [], goals::stk, acc => go n p goals stk acc
  | n, p, g::goals, stk, acc => do
    if ← g.isAssigned then
      go n p goals stk acc
    else
      match n with
      | 0 => pure <| (p, acc.push g ++ goals |> stk.foldl .appendList)
      | n+1 =>
        match ← observing? (f g) with
        | some goals' => go n true goals' (goals::stk) acc
        | none => go n p goals stk (acc.push g)
termination_by n _ goals stk => (n, stk, goals)

/--
`repeat' f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.
Always succeeds (returning the original goals if `f` fails on all of them).
-/
def repeat' [Monad m] [MonadExcept ε m] [MonadBacktrack s m] [MonadMCtx m]
    (f : MVarId → m (List MVarId)) (goals : List MVarId) (maxIters := 100000) : m (List MVarId) :=
  repeat'Core f goals maxIters <&> (·.2)

/--
`repeat1' f` runs `f` on all of the goals to produce a new list of goals,
then runs `f` again on all of those goals, and repeats until `f` fails on all remaining goals,
or until `maxIters` total calls to `f` have occurred.
Fails if `f` does not succeed at least once.
-/
def repeat1' [Monad m] [MonadError m] [MonadExcept ε m] [MonadBacktrack s m] [MonadMCtx m]
    (f : MVarId → m (List MVarId)) (goals : List MVarId) (maxIters := 100000) : m (List MVarId) := do
  let (.true, goals) ← repeat'Core f goals maxIters | throwError "repeat1' made no progress"
  pure goals

end Lean.Meta
