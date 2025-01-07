/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Lean.Meta.LitValues
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Util

namespace Lean.Meta.Grind

/-- Adds `e` to congruence table. -/
def addCongrTable (e : Expr) : GoalM Unit := do
  if let some { e := e' } := (← get).congrTable.find? { e } then
    -- `f` and `g` must have the same type.
    -- See paper: Congruence Closure in Intensional Type Theory
    let f := e.getAppFn
    let g := e'.getAppFn
    unless isSameExpr f g do
      unless (← hasSameType f g) do
        trace[grind.issues] "found congruence between{indentExpr e}\nand{indentExpr e'}\nbut functions have different types"
        return ()
    trace[grind.debug.congr] "{e} = {e'}"
    pushEqHEq e e' congrPlaceholderProof
    let node ← getENode e
    setENode e { node with congr := e' }
  else
    modify fun s => { s with congrTable := s.congrTable.insert { e } }

/--
Given an application `e` of the form `f a_1 ... a_n`,
adds entry `f ↦ e` to `appMap`. Recall that `appMap` is a multi-map.
-/
private def updateAppMap (e : Expr) : GoalM Unit := do
  let key := e.toHeadIndex
  modify fun s => { s with
    appMap := if let some es := s.appMap.find? key then
      s.appMap.insert key (e :: es)
    else
      s.appMap.insert key [e]
  }

/-- Inserts `e` into the list of case-split candidates. -/
private def addSplitCandidate (e : Expr) : GoalM Unit := do
  trace[grind.split.candidate] "{e}"
  modify fun s => { s with splitCandidates := e :: s.splitCandidates }

-- TODO: add attribute to make this extensible
private def forbiddenSplitTypes := [``Eq, ``HEq, ``True, ``False]

/-- Inserts `e` into the list of case-split candidates if applicable. -/
private def checkAndAddSplitCandidate (e : Expr) : GoalM Unit := do
  unless e.isApp do return ()
  if e.isIte || e.isDIte then
    addSplitCandidate e
  else if (← isMatcherApp e) then
    if let .reduced _ ← reduceMatcher? e then
      -- When instantiating `match`-equations, we add `match`-applications that can be reduced,
      -- and consequently don't need to be splitted.
      return ()
    else
      addSplitCandidate e
  else
    let .const declName _  := e.getAppFn | return ()
    if forbiddenSplitTypes.contains declName then return ()
    -- We should have a mechanism for letting users to select types to case-split.
    -- Right now, we just consider inductive predicates that are not in the forbidden list
    if (← isInductivePredicate declName) then
      addSplitCandidate e

mutual
/-- Internalizes the nested ground terms in the given pattern. -/
private partial def internalizePattern (pattern : Expr) (generation : Nat) : GoalM Expr := do
  if pattern.isBVar || isPatternDontCare pattern then
    return pattern
  else if let some e := groundPattern? pattern then
    let e ← shareCommon (← canon (← normalizeLevels (← unfoldReducible e)))
    internalize e generation
    return mkGroundPattern e
  else pattern.withApp fun f args => do
    return mkAppN f (← args.mapM (internalizePattern · generation))

private partial def activateTheorem (thm : EMatchTheorem) (generation : Nat) : GoalM Unit := do
  -- Recall that we use the proof as part of the key for a set of instances found so far.
  -- We don't want to use structural equality when comparing keys.
  let proof ← shareCommon thm.proof
  let thm := { thm with proof, patterns := (← thm.patterns.mapM (internalizePattern · generation)) }
  trace[grind.ematch] "activated `{thm.origin.key}`, {thm.patterns.map ppPattern}"
  modify fun s => { s with newThms := s.newThms.push thm }

/--
If `Config.matchEqs` is set to `true`, and `f` is `match`-auxiliary function,
adds its equations to `newThms`.
-/
private partial def addMatchEqns (f : Expr) (generation : Nat) : GoalM Unit := do
  if !(← getConfig).matchEqs then return ()
  let .const declName _ := f | return ()
  if !(← isMatcher declName) then return ()
  if (← get).matchEqNames.contains declName then return ()
  modify fun s => { s with matchEqNames := s.matchEqNames.insert declName }
  for eqn in (← Match.getEquationsFor declName).eqnNames do
    -- We disable pattern normalization to prevent the `match`-expression to be reduced.
    activateTheorem (← mkEMatchEqTheorem eqn (normalizePattern := false)) generation

private partial def activateTheoremPatterns (fName : Name) (generation : Nat) : GoalM Unit := do
  if let some (thms, thmMap) := (← get).thmMap.retrieve? fName then
    modify fun s => { s with thmMap }
    let appMap := (← get).appMap
    for thm in thms do
      let symbols := thm.symbols.filter fun sym => !appMap.contains sym
      let thm := { thm with symbols }
      match symbols with
      | [] => activateTheorem thm generation
      | _ =>
        trace[grind.ematch] "reinsert `{thm.origin.key}`"
        modify fun s => { s with thmMap := s.thmMap.insert thm }

partial def internalize (e : Expr) (generation : Nat) : GoalM Unit := do
  if (← alreadyInternalized e) then return ()
  trace[grind.internalize] "{e}"
  match e with
  | .bvar .. => unreachable!
  | .sort .. => return ()
  | .fvar .. | .letE .. | .lam .. =>
    mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)
  | .forallE _ d b _ =>
    mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)
    if (← isProp d <&&> isProp e) then
      internalize d generation
      registerParent e d
      unless b.hasLooseBVars do
        internalize b generation
        registerParent e b
      propagateUp e
  | .lit .. | .const .. =>
    mkENode e generation
  | .mvar ..
  | .mdata ..
  | .proj .. =>
    trace[grind.issues] "unexpected term during internalization{indentExpr e}"
    mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)
  | .app .. =>
    if (← isLitValue e) then
      -- We do not want to internalize the components of a literal value.
      mkENode e generation
    else e.withApp fun f args => do
      checkAndAddSplitCandidate e
      addMatchEqns f generation
      if f.isConstOf ``Lean.Grind.nestedProof && args.size == 2 then
        -- We only internalize the proposition. We can skip the proof because of
        -- proof irrelevance
        let c := args[0]!
        internalize c generation
        registerParent e c
      else
        if let .const fName _ := f then
          activateTheoremPatterns fName generation
        else
          internalize f generation
          registerParent e f
        for h : i in [: args.size] do
          let arg := args[i]
          internalize arg generation
          registerParent e arg
      mkENode e generation
      addCongrTable e
      updateAppMap e
      propagateUp e
end

end Lean.Meta.Grind
