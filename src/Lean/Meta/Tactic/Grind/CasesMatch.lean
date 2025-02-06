/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Cases
import Lean.Meta.Match.MatcherApp
import Lean.Meta.Tactic.Grind.MatchCond

namespace Lean.Meta.Grind

/-- Returns `true` if `e` is of the form `∀ ..., _ = _ ... -> False` -/
def isMatchCondCandidate (e : Expr) : Bool :=
  -- TODO: see comment at the beginning of `MatchCond.lean`.
  Simp.isEqnThmHypothesis e

/--
Given a splitter alternative, annotate the terms that are `match`-expression
conditions corresponding to overlapping patterns.
-/
private def addMatchCondsToAlt (alt : Expr) : Expr := Id.run do
  let .forallE _ d b _ := alt
    | return alt
  let d := if isMatchCondCandidate d then markAsMatchCond d else d
  return alt.updateForallE! d (addMatchCondsToAlt b)

/--
Annotates the `match`-expression conditions in the alternatives in the given
`match` splitter type.
-/
private def addMatchCondsToSplitter (splitterType : Expr) (numAlts : Nat) : Expr := Id.run do
  if numAlts == 0 then return splitterType
  let .forallE _ alt b _ := splitterType
    | return splitterType
  return splitterType.updateForallE! (addMatchCondsToAlt alt) (addMatchCondsToSplitter b (numAlts-1))

def casesMatch (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) := mvarId.withContext do
  let some app ← matchMatcherApp? e
    | throwTacticEx `grind.casesMatch mvarId m!"`match`-expression expected{indentExpr e}"
  let (motive, eqRefls) ← mkMotiveAndRefls app
  let target ← mvarId.getType
  let mut us := app.matcherLevels
  if let some i := app.uElimPos? then
    us := us.set! i (← getLevel target)
  let splitterName := (← Match.getEquationsFor app.matcherName).splitterName
  let splitterApp := mkConst splitterName us.toList
  let splitterApp := mkAppN splitterApp app.params
  let splitterApp := mkApp splitterApp motive
  let splitterApp := mkAppN splitterApp app.discrs
  let numAlts := app.alts.size
  let splitterType ← inferType splitterApp
  let splitterType := addMatchCondsToSplitter splitterType app.alts.size
  let (mvars, _, _) ← forallMetaBoundedTelescope splitterType numAlts (kind := .syntheticOpaque)
  let splitterApp := mkAppN splitterApp mvars
  let val := mkAppN splitterApp eqRefls
  mvarId.assign val
  updateTags mvars
  return mvars.toList.map (·.mvarId!)
where
  mkMotiveAndRefls (app : MatcherApp) : MetaM (Expr × Array Expr) := do
    let dummy := mkSort 0
    let aux := mkApp (mkAppN e.getAppFn app.params) dummy
    forallBoundedTelescope (← inferType aux) app.discrs.size fun xs _ => do
    withNewEqs app.discrs xs fun eqs eqRefls => do
      let type ← mvarId.getType
      let type ← mkForallFVars eqs type
      let motive ← mkLambdaFVars xs type
      return (motive, eqRefls)

  updateTags (mvars : Array Expr) : MetaM Unit := do
    let tag ← mvarId.getTag
    if mvars.size == 1 then
      mvars[0]!.mvarId!.setTag tag
    else
      let mut idx := 1
      for mvar in mvars do
        mvar.mvarId!.setTag (Name.num tag idx)
        idx := idx + 1

end Lean.Meta.Grind
