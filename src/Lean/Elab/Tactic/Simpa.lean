/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Mario Carneiro
-/
prelude
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.Simp
import Lean.Elab.App
import Lean.Linter.Basic

/--
Enables the 'unnecessary `simpa`' linter. This will report if a use of
`simpa` could be proven using `simp` or `simp at h` instead.
-/
register_option linter.unnecessarySimpa : Bool := {
  defValue := true
  descr := "enable the 'unnecessary simpa' linter"
}

namespace Lean.Elab.Tactic.Simpa

open Lean Parser.Tactic Elab Meta Term Tactic Simp Linter

/-- Gets the value of the `linter.unnecessarySimpa` option. -/
def getLinterUnnecessarySimpa (o : Options) : Bool :=
  getLinterValue linter.unnecessarySimpa o

deriving instance Repr for UseImplicitLambdaResult

@[builtin_tactic Lean.Parser.Tactic.simpa] def evalSimpa : Tactic := fun stx => do
  match stx with
  | `(tactic| simpa%$tk $[?%$squeeze]? $[!%$unfold]? $cfg:optConfig $(disch)? $[only%$only]?
        $[[$args,*]]? $[using $usingArg]?) => Elab.Tactic.focus do withSimpDiagnostics do
    let stx ← `(tactic| simp $cfg:optConfig $(disch)? $[only%$only]? $[[$args,*]]?)
    let { ctx, simprocs, dischargeWrapper } ←
      withMainContext <| mkSimpContext stx (eraseLocal := false)
    let ctx := if unfold.isSome then { ctx with config.autoUnfold := true } else ctx
    -- TODO: have `simpa` fail if it doesn't use `simp`.
    let ctx := { ctx with config := { ctx.config with failIfUnchanged := false } }
    dischargeWrapper.with fun discharge? => do
      let (some (_, g), stats) ← simpGoal (← getMainGoal) ctx (simprocs := simprocs)
          (simplifyTarget := true) (discharge? := discharge?)
        | if getLinterUnnecessarySimpa (← getOptions) then
            logLint linter.unnecessarySimpa (← getRef) "try 'simp' instead of 'simpa'"
          return {}
      g.withContext do
      let stats ← if let some stx := usingArg then
        let mvarCounterSaved := (← getMCtx).mvarCounter
        let e ← Tactic.elabTerm stx none (mayPostpone := true)
        unless ← occursCheck g e do
          throwError "occurs check failed, expression{indentExpr e}\ncontains the goal {Expr.mvar g}"
        -- Copy the goal. We want to defer assigning `g := g'` to prevent `MVarId.note` from
        -- partially assigning the goal in case we need to log unassigned metavariables.
        -- Without deferring, this can cause `logUnassignedAndAbort` to report that `g` could not
        -- be synthesized; recall that this function reports that a metavariable could not be
        -- synthesized if, after mvar instantiation, it contains one of the provided mvars.
        let gCopy ← mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        let (h, g') ← gCopy.mvarId!.note `h e
        let (result?, stats) ← simpGoal g' ctx (simprocs := simprocs) (fvarIdsToSimp := #[h])
          (simplifyTarget := false) (stats := stats) (discharge? := discharge?)
        match result? with
        | some (xs, g') =>
          let h := xs[0]?.getD h
          let name ← mkFreshUserName `h
          let g' ← g'.rename h name
          setGoals [g']
          g'.withContext do
            let gType ← g'.getType
            let h ← Term.elabTerm (mkIdent name) gType
            Term.synthesizeSyntheticMVarsNoPostponing
            let hType ← inferType h
            unless (← withAssignableSyntheticOpaque <| isDefEq gType hType) do
              -- `e` still is valid in this new local context
              Term.throwTypeMismatchError gType hType h
                (header? := some m!"type mismatch, term{indentExpr e}\nafter simplification")
            logUnassignedAndAbort (← filterOldMVars (← getMVars e) mvarCounterSaved)
            closeMainGoal `simpa (checkUnassigned := false) h
        | none =>
          if getLinterUnnecessarySimpa (← getOptions) then
            if let .fvar h := e then
              if (← getLCtx).getRoundtrippingUserName? h |>.isSome then
                logLint linter.unnecessarySimpa (← getRef)
                  m!"try 'simp at {Expr.fvar h}' instead of 'simpa using {Expr.fvar h}'"
        g.assign gCopy
        pure stats
      else if let some ldecl := (← getLCtx).findFromUserName? `this then
        if let (some (_, g), stats) ← simpGoal g ctx (simprocs := simprocs)
            (fvarIdsToSimp := #[ldecl.fvarId]) (simplifyTarget := false) (stats := stats)
            (discharge? := discharge?) then
          g.assumption; pure stats
        else
          pure stats
      else
        g.assumption; pure stats
      if tactic.simp.trace.get (← getOptions) || squeeze.isSome then
        let usingArg : Option Term := usingArg.map (⟨·.raw.unsetTrailing⟩)
        let stx ← match ← mkSimpOnly stx.raw.unsetTrailing stats.usedTheorems with
          | `(tactic| simp $cfg:optConfig $(disch)? $[only%$only]? $[[$args,*]]?) =>
            if unfold.isSome then
              `(tactic| simpa! $cfg:optConfig $(disch)? $[only%$only]? $[[$args,*]]? $[using $usingArg]?)
            else
              `(tactic| simpa $cfg:optConfig $(disch)? $[only%$only]? $[[$args,*]]? $[using $usingArg]?)
          | _ => unreachable!
        TryThis.addSuggestion tk stx (origSpan? := ← getRef)
      return stats.diag
    | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Simpa
