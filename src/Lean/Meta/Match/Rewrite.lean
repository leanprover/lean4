/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp.Rewrite

public section

namespace Lean.Meta

/--
Tries to rewrite the `ite`, `dite` or `cond` expression `e` with the hypothesis `hc`.
If it fails, it returns a rewrite with `proof? := none` and unchanged expression.
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
def rwMatcher (altIdx : Nat) (e : Expr) (assumptionLowerBound : Nat := 0)
    (assumptionUpperBound : Nat := 0) : MetaM Simp.Result := do
  -- Close `g` by an assumption at context index in `[assumptionLowerBound, assumptionUpperBound)`, so
  -- the search for the congruence-equation hypotheses is confined to a window of the local context.
  let assumptionProc (g : MVarId) : MetaM Bool :=
    g.assumptionCore assumptionLowerBound assumptionUpperBound
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
    -- Close an `Eq`/`HEq` hypothesis `h` by reflexivity without throwing when it is not reflexive.
    let tryRefl (h : MVarId) (hType : Expr) : MetaM Bool := do
      if let some (_, a, b) := hType.eq? then
        unless ← isDefEq a b do return false
        h.assign (← mkEqRefl a)
        return true
      if let some (α, a, β, b) := hType.heq? then
        unless ← (isDefEq α β <&&> isDefEq a b) do return false
        h.assign (← mkHEqRefl a)
        return true
      return false
    try
      withTraceNode `Meta.Match.debug (fun _ => pure m!"rewriting with {.ofConstName eqnThm} in{indentExpr e}") do
      let eqProof := mkAppN (mkConst eqnThm e.getAppFn.constLevels!) e.getAppArgs
      let (hyps, _, eqType) ← forallMetaTelescope (← inferType eqProof)
      trace[Meta.Match.debug] "eqProof has type{indentExpr eqType}"
      let proof := mkAppN eqProof hyps
      let hyps := hyps.map (·.mvarId!)
      let (isHeq, lhs, rhs) ← do
        if let some (_, lhs, _, rhs) := eqType.heq? then pure (true, lhs, rhs) else
        if let some (_, lhs, rhs) := eqType.eq? then pure (false, lhs, rhs) else
        throwError m!"Type of `{.ofConstName eqnThm}` is not an equality"
      -- The alternative not applying here (`isDefEq`/discharge failure below) is a normal outcome
      -- reported via `proof? := none`, not an error: callers probing alternatives must not pay for
      -- exception handling on each miss.
      if !(← isDefEq e lhs) then return { expr := e }
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
          let discharged ←
            if Simp.isEqnThmHypothesis hType then
              -- Using unrestricted h.substVars here does not work well; it could
              -- even introduce a dependency on the `oldIH` we want to eliminate
              assumptionProc h
            else if hType.isEq || hType.isHEq then
              assumptionProc h <||> tryRefl h hType
            else
              pure true
          unless discharged do return { expr := e }
      if ← hyps.anyM fun h => return !(← h.isAssigned) then
        return { expr := e }
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
