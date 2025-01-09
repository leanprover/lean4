/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Init.Simproc
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.Match.Lift
import Lean.Meta.KAbstract
import Lean.Elab.Tactic.Conv.Basic

/-!
This module implements the `liftMatch` simpproc and the `lift_match` conv tactic.
-/


open Lean Meta Elab Term

namespace Lean.Meta

section LiftMatch

inductive MatcherOrIteApp where
  | matcher (matcherApp : MatcherApp)
  | ite (dite : Bool) (α P inst t e : Expr)

private def _root_.Lean.Expr.constLams? : Expr → Option Expr
  | .lam _ _ b _ => constLams? b
  | e => if e.hasLooseBVars then none else some e

def MatcherOrIteApp.motive? : MatcherOrIteApp -> Option Expr
  | matcher matcherApp => matcherApp.motive.constLams?
  | ite _ α _ _ _ _ => some α

def mkMatchOrIteLiftApp (f : Expr) (moi : MatcherOrIteApp) : MetaM (Option Expr) := do
  match moi with
  | .matcher matcherApp => mkMatchLifterApp f matcherApp
  | .ite dite α P inst t e =>
      let some (_, β) := (← inferType f).arrow? |
        trace[lift_match] "Cannot lift match: {f} is dependent"
        return none
      let lifterName := if dite then ``apply_dite else ``apply_ite
      let e ← mkAppOptM lifterName #[some α, some β, some f, some P, some inst, some t, some e]
      return some e


/--
Like matchMatcherApp, but also matches ite/dite.
-/
private def matchMatcherOrIteApp? (e : Expr) : MetaM (Option MatcherOrIteApp) := do
  match_expr e with
  | ite α P inst t e => return some (.ite false α P inst t e)
  | dite α P inst t e => return some (.ite true α P inst t e)
  | _ =>
    if let some matcherApp ← matchMatcherApp? e then
      if matcherApp.remaining.isEmpty then
        return .some (.matcher matcherApp)
  return none

/--
Finds the first possible liftable match (or (d)ite).
-/
private partial def findMatchToLift? (e : Expr) (far : Bool) (depth : Nat := 0) : MetaM (Option (Expr × MatcherOrIteApp)) := do
  if !far && depth > 1 then
    return none

  if e.isApp then
    if depth > 0 then
      if let some matcherApp ← matchMatcherOrIteApp? e then
        return some (e, matcherApp)


    let args := e.getAppArgs
    if e.isAppOf ``ite then
      -- Special-handling for if-then-else:
      -- * We do not want to lift out of the branches.
      -- * We want to be able to lift out of
      --      @ite ([ ] = true) (instDecidableEqBool [ ] true) t e
      --   but doing it one application at a time does not work due to the dependency.
      --   So to work around this, we do not bump the depth counter here.
      if h : args.size > 1 then
        if let some r ← findMatchToLift? args[1] far depth then
          return some r
    else
      for a in args do
        if let some r ← findMatchToLift? a far (depth + 1) then
          return some r

  if e.isLet then
    if let some r ← findMatchToLift? e.letValue! far (depth + 1) then
      return some r

  return none

/--
In `e`, try to find a `match` expression or `ite` application that we can lift
to the root. Returns the new expression `s` and a proof of `e = s`.
-/
def findAndLiftMatch (e : Expr) (far : Bool) : MetaM (Option (Expr × Expr)) := do
  unless far do
    -- In the simproc: We could, but for now we do not lift out of props
    if ← Meta.isProp e then return none
  let some (me, matcherApp) ← findMatchToLift? e far| return none
  -- We do not handle dependent motives
  let some α := matcherApp.motive? |
    trace[lift_match] "Cannot lift match: motive depends on targets"
    return none
  -- Using kabstract, rather than just abstracting over the single occurrence of `me` in `e` with
  -- helps if later arguments depend on the abstracted argument,
  -- in particular with ``ite's `Decidable c` parameter
  let f := (mkLambda `x .default α (← kabstract e me)).eta
  -- Abstracting over the argument can result in a type incorrect `f` (like in `rw`)
  unless (← isTypeCorrect f) do
    trace[lift_match] "Cannot lift match: context is not type correct"
    return none
  let some proof ← mkMatchOrIteLiftApp f matcherApp | return none
  let type ← inferType proof
  let some (_, _, rhs) := type.eq?
    | throwError "lift_match: Unexpected non-equality type:{indentExpr type}"
  return some (rhs, proof)

end LiftMatch

end Lean.Meta

/-!
The simproc tactic
-/

section Simproc

/--
Lifts out `match` expressions, or, equivalently, pushes function applications into the
branches of a match. For example it can rewrite
```
f (match o with | some x => x + 1 | none => 0)
```
to
```
match o with | some x => f (x + 1) | none => f 0
```

For the purposes of this simproc, `if-then-else` expressions are treated like `match` expressions.

It can only lift matches with a non-dependent motive, no extra arguments and when the context
(here `fun x => f x`) is type-correct and is not a proposition.

It is recommended to enable this simproc only selectively, and not by default, as it looks for
match expression to lift at every step of the simplifier.

Also see the `conv`-tactic `lift_match`.
-/
builtin_simproc_decl liftMatch (_) := fun e => do
  let some (rhs, proof) ← findAndLiftMatch (far := false) e | return .continue
  return .visit { expr := rhs, proof? := some proof }

end Simproc


/-!
The conv tactic
-/

namespace Lean.Elab.Tactic.Conv

@[builtin_tactic Lean.Parser.Tactic.Conv.liftMatch]
def evalLiftMatch : Tactic := fun _ => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lhs ← getLhs
    let some (rhs, proof) ← findAndLiftMatch (far := true) lhs
      | throwError "cannot find match to lift"
    updateLhs rhs proof

end Lean.Elab.Tactic.Conv
