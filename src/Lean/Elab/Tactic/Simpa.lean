/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Mario Carneiro
-/
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.Simp
import Lean.Linter.Util

/--
Enables the 'unnecessary `simpa`' linter. This will report if a use of
`simpa` could be proven using `simp` or `simp at h` instead.
-/
register_option linter.unnecessarySimpa : Bool := {
  defValue := true
  descr := "enable the 'unnecessary simpa' linter"
}

namespace Std.Tactic.Simpa

open Lean Parser.Tactic Elab Meta Term Tactic Simp Linter

/--
A `simpArg` is either a `*`, `-lemma` or a simp lemma specification
(which includes the `↑` `↓` `←` specifications for pre, post, reverse rewriting).
-/
def simpArg := simpStar.binary `orelse (simpErase.binary `orelse simpLemma)

/-- A simp args list is a list of `simpArg`. This is the main argument to `simp`. -/
syntax simpArgs := " [" simpArg,* "]"

/--
A `dsimpArg` is similar to `simpArg`, but it does not have the `simpStar` form
because it does not make sense to use hypotheses in `dsimp`.
-/
def dsimpArg := simpErase.binary `orelse simpLemma

/-- A dsimp args list is a list of `dsimpArg`. This is the main argument to `dsimp`. -/
syntax dsimpArgs := " [" dsimpArg,* "]"

/-- The arguments to the `simpa` family tactics. -/
syntax simpaArgsRest := (config)? (discharger)? &" only "? (simpArgs)? (" using " term)?

/--
This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

  Simplifying the type of `e` makes it more likely to match the goal
  (which has also been simplified). This construction also tends to be
  more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
  hypothesis `this` if present in the context, then try to close the goal using
  the `assumption` tactic.

#TODO: implement `?`
-/
syntax (name := simpa) "simpa" "?"? "!"? simpaArgsRest : tactic
@[inherit_doc simpa] macro "simpa!" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ! $rest:simpaArgsRest)
@[inherit_doc simpa] macro "simpa?" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ? $rest:simpaArgsRest)
@[inherit_doc simpa] macro "simpa?!" rest:simpaArgsRest : tactic =>
  `(tactic| simpa ?! $rest:simpaArgsRest)

/-- Gets the value of the `linter.unnecessarySimpa` option. -/
def getLinterUnnecessarySimpa (o : Options) : Bool :=
  getLinterValue linter.unnecessarySimpa o

deriving instance Repr for UseImplicitLambdaResult

elab_rules : tactic
| `(tactic| simpa%$tk $[?%$squeeze]? $[!%$unfold]? $(cfg)? $(disch)? $[only%$only]?
      $[[$args,*]]? $[using $usingArg]?) => Elab.Tactic.focus do
  let stx ← `(tactic| simp $(cfg)? $(disch)? $[only%$only]? $[[$args,*]]?)
  let { ctx, simprocs, dischargeWrapper } ←
    withMainContext <| mkSimpContext stx (eraseLocal := false)
  let ctx := if unfold.isSome then { ctx with config.autoUnfold := true } else ctx
  -- TODO: have `simpa` fail if it doesn't use `simp`.
  let ctx := { ctx with config := { ctx.config with failIfUnchanged := false } }
  dischargeWrapper.with fun discharge? => do
    let (some (_, g), usedSimps) ← simpGoal (← getMainGoal) ctx (simprocs := simprocs)
        (simplifyTarget := true) (discharge? := discharge?)
      | if getLinterUnnecessarySimpa (← getOptions) then
          logLint linter.unnecessarySimpa (← getRef) "try 'simp' instead of 'simpa'"
    g.withContext do
    let usedSimps ← if let some stx := usingArg then
      setGoals [g]
      g.withContext do
      let e ← Tactic.elabTerm stx none (mayPostpone := true)
      let (h, g) ← if let .fvar h ← instantiateMVars e then
        pure (h, g)
      else
        (← g.assert `h (← inferType e) e).intro1
      let (result?, usedSimps) ← simpGoal g ctx (simprocs := simprocs) (fvarIdsToSimp := #[h])
        (simplifyTarget := false) (usedSimps := usedSimps) (discharge? := discharge?)
      match result? with
      | some (xs, g) =>
        let h := match xs with | #[h] | #[] => h | _ => unreachable!
        let name ← mkFreshBinderNameForTactic `h
        let g ← g.rename h name
        g.assign <|← g.withContext do
          Tactic.elabTermEnsuringType (mkIdent name) (← g.getType)
      | none =>
        if getLinterUnnecessarySimpa (← getOptions) then
          if (← getLCtx).getRoundtrippingUserName? h |>.isSome then
            logLint linter.unnecessarySimpa (← getRef)
              m!"try 'simp at {Expr.fvar h}' instead of 'simpa using {Expr.fvar h}'"
      pure usedSimps
    else if let some ldecl := (← getLCtx).findFromUserName? `this then
      if let (some (_, g), usedSimps) ← simpGoal g ctx (simprocs := simprocs)
          (fvarIdsToSimp := #[ldecl.fvarId]) (simplifyTarget := false) (usedSimps := usedSimps)
          (discharge? := discharge?) then
        g.assumption; pure usedSimps
      else
        pure usedSimps
    else
      g.assumption; pure usedSimps
    if tactic.simp.trace.get (← getOptions) || squeeze.isSome then
      let stx ← match ← mkSimpOnly stx usedSimps with
        | `(tactic| simp $(cfg)? $(disch)? $[only%$only]? $[[$args,*]]?) =>
          if unfold.isSome then
            `(tactic| simpa! $(cfg)? $(disch)? $[only%$only]? $[[$args,*]]? $[using $usingArg]?)
          else
            `(tactic| simpa $(cfg)? $(disch)? $[only%$only]? $[[$args,*]]? $[using $usingArg]?)
        | _ => unreachable!
      TryThis.addSuggestion tk stx (origSpan? := ← getRef)
