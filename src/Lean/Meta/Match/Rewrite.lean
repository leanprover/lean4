/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp.Rewrite

public section

namespace Lean.Meta

/--
Tries to rewrite the `ite`, `dite` or `cond` expression `e` with the hypothesis `hc`.
If it fails, it returns a rewrite with `proof? := none` and unchaged expression.
-/
def rwIfWith (hc : Expr) (e : Expr) : MetaM Simp.Result := do
  match_expr e with
  | ite@ite α c h t f =>
    let us := ite.constLevels!
    if (← isDefEq c (← inferType hc)) then
      return {
        expr := t
        proof? := (mkAppN (mkConst ``if_pos us) #[c, h, hc, α, t, f])
      }
    if (← isDefEq (mkNot c) (← inferType hc)) then
      return {
        expr := f
        proof? := (mkAppN (mkConst ``if_neg us) #[c, h, hc, α, t, f])
      }
  | dite@dite α c h t f =>
    let us := dite.constLevels!
    if (← isDefEq c (← inferType hc)) then
      return {
        expr := t.beta #[hc]
        proof? := (mkAppN (mkConst ``dif_pos us) #[c, h, hc, α, t, f])
      }
    if (← isDefEq (mkNot c) (← inferType hc)) then
      return {
        expr := f.beta #[hc]
        proof? := (mkAppN (mkConst ``dif_neg us) #[c, h, hc, α, t, f])
      }
  | cond@cond α c t f =>
    let us := cond.constLevels!
    if (← isDefEq (← inferType hc) (← mkEq c (mkConst ``Bool.true))) then
      return {
        expr := t
        proof? := (mkAppN (mkConst ``Bool.cond_pos us) #[α, c, t, f, hc])
      }
    if (← isDefEq (← inferType hc) (← mkEq c (mkConst ``Bool.false))) then
      return {
        expr := f
        proof? := (mkAppN (mkConst ``Bool.cond_neg us) #[α, c, t, f, hc])
      }
  | _ => pure ()
  return { expr := e }

/--
In the `onAlt` handler of a `MatcherApp.transform`, you can use this function on a properly
substituted matcher application with the alternative `altIdx`.

If it fails, it returns a rewrite with `proof? := none` and the unchanged expression.

"Properly substituted" here means that the discriminants have been substituted according to the
alternative; otherwise, the rewrite might fail because some hypothesis of the congruence
equation theorem cannot be discharged by assumption or reflixivity.
See `Lean.Meta.Tactic.FunInd.buildInductionBody` and `Lean.Elab.Tactic.Do.VCGen.Split` for examples
of how to coerce `MatherApp.transform` into doing the substitution on the motive for you.
-/
def rwMatcher (altIdx : Nat) (e : Expr) : MetaM Simp.Result := do
  if e.isAppOf ``PSum.casesOn || e.isAppOf ``PSigma.casesOn then
    let mut e := e
    while true do
      if let some e' ← reduceRecMatcher? e then
          e := e'.headBeta
      else
        let e' := e.headBeta
        if e != e' then
          e := e'
        else
          break
    return { expr := e }
  else
    unless (← isMatcherApp e) do
      trace[Meta.Match.debug] "Not a matcher application:{indentExpr e}"
      return { expr := e }
    let matcherDeclName := e.getAppFn.constName!
    let eqns ← Match.genMatchCongrEqns matcherDeclName
    unless altIdx < eqns.size do
      trace[Meta.Match.debug] "When trying to reduce arm {altIdx}, only {eqns.size} equations for {.ofConstName matcherDeclName}"
      return { expr := e }
    let eqnThm := eqns[altIdx]!
    try
      withTraceNode `Meta.Match.debug (pure m!"{exceptEmoji ·} rewriting with {.ofConstName eqnThm} in{indentExpr e}") do
      let eqProof := mkAppN (mkConst eqnThm e.getAppFn.constLevels!) e.getAppArgs
      let (hyps, _, eqType) ← forallMetaTelescope (← inferType eqProof)
      trace[Meta.Match.debug] "eqProof has type{indentExpr eqType}"
      let proof := mkAppN eqProof hyps
      let hyps := hyps.map (·.mvarId!)
      let (isHeq, lhs, rhs) ← do
        if let some (_, lhs, _, rhs) := eqType.heq? then pure (true, lhs, rhs) else
        if let some (_, lhs, rhs) := eqType.eq? then pure (false, lhs, rhs) else
        throwError m!"Type of `{.ofConstName eqnThm}` is not an equality"
      if !(← isDefEq e lhs) then
        throwError m!"Left-hand side `{lhs}` of `{.ofConstName eqnThm}` does not apply to `{e}`"
      /-
      Here we instantiate the hypotheses of the congruence equation theorem
      There are two sets of hypotheses to instantiate:
      - `Eq` or `HEq` that relate the discriminants to the patterns
        Solving these should instantiate the pattern variables.
      - Overlap hypotheses (`isEqnThmHypothesis`)
      With more book keeping we could maybe do this very precisely, knowing exactly
      which facts provided by the splitter should go where, but it's tedious.
      So for now let's use heuristics and try `assumption` and `rfl`.
      -/
      for h in hyps do
        unless (← h.isAssigned) do
          let hType ← h.getType
          if Simp.isEqnThmHypothesis hType then
            -- Using unrestricted h.substVars here does not work well; it could
            -- even introduce a dependency on the `oldIH` we want to eliminate
            h.assumption <|> throwError "Failed to discharge `{h}`"
          else if hType.isEq then
            h.assumption <|> h.refl <|> throwError m!"Failed to resolve `{h}`"
          else if hType.isHEq then
            h.assumption <|> h.hrefl <|> throwError m!"Failed to resolve `{h}`"
      let unassignedHyps ← hyps.filterM fun h => return !(← h.isAssigned)
      unless unassignedHyps.isEmpty do
        throwError m!"Not all hypotheses of `{.ofConstName eqnThm}` could be discharged: {unassignedHyps}"
      let rhs ← instantiateMVars rhs
      let proof ← instantiateMVars proof
      let proof ← if isHeq then
          try mkEqOfHEq proof
          catch e => throwError m!"Could not un-HEq `{proof}`:{indentD e.toMessageData} "
        else
          pure proof
      return {
        expr := rhs
        proof? := proof
      }
    catch ex =>
      trace[Meta.Match.debug] "Failed to apply {.ofConstName eqnThm}:{indentD ex.toMessageData}"
      return { expr := e }
