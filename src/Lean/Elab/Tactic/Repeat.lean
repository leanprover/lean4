/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/

import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Cases

open Lean Elab Tactic

/--
`iterate n tac` runs `tac` exactly `n` times.
`iterate tac` runs `tac` repeatedly until failure.

`iterate`'s argument is a tactic sequence,
so multiple tactics can be run using `iterate n (tac₁; tac₂; ⋯)` or
```lean
iterate n
  tac₁
  tac₂
  ⋯
```
-/
syntax "iterate" (ppSpace num)? ppSpace tacticSeq : tactic
macro_rules
  | `(tactic| iterate $seq:tacticSeq) =>
    `(tactic| try ($seq:tacticSeq); iterate $seq:tacticSeq)
  | `(tactic| iterate $n $seq:tacticSeq) =>
    match n.1.toNat with
    | 0 => `(tactic| skip)
    | n+1 => `(tactic| ($seq:tacticSeq); iterate $(quote n) $seq:tacticSeq)

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
termination_by n p goals stk _ => (n, stk, goals)

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

/--
`repeat' tac` runs `tac` on all of the goals to produce a new list of goals,
then runs `tac` again on all of those goals, and repeats until `tac` fails on all remaining goals.
-/
elab "repeat' " tac:tacticSeq : tactic => do
  setGoals (← repeat' (evalTacticAtRaw tac) (← getGoals))

/--
`repeat1' tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
elab "repeat1' " tac:tacticSeq : tactic => do
  setGoals (← repeat1' (evalTacticAtRaw tac) (← getGoals))

/-- `split_ands` applies `And.intro` until it does not make progress. -/
syntax "split_ands" : tactic
macro_rules | `(tactic| split_ands) => `(tactic| repeat' refine And.intro ?_ ?_)
