/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Init.Grind.Lemmas
import Lean.Meta.LitValues
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Canon
import Lean.Meta.Tactic.Grind.Beta
import Lean.Meta.Tactic.Grind.MatchCond
import Lean.Meta.Tactic.Grind.Arith.Internalize

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
        reportIssue! "found congruence between{indentExpr e}\nand{indentExpr e'}\nbut functions have different types"
        return ()
    trace_goal[grind.debug.congr] "{e} = {e'}"
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
  trace_goal[grind.split.candidate] "{e}"
  modify fun s => { s with split.candidates := e :: s.split.candidates }

private def forbiddenSplitTypes := [``Eq, ``HEq, ``True, ``False]

/-- Returns `true` if `e` is of the form `@Eq Prop a b` -/
def isMorallyIff (e : Expr) : Bool :=
  let_expr Eq α _ _ := e | false
  α.isProp

/-- Inserts `e` into the list of case-split candidates if applicable. -/
private def checkAndAddSplitCandidate (e : Expr) : GoalM Unit := do
  match e with
  | .app .. =>
    if (← getConfig).splitIte && (e.isIte || e.isDIte) then
      addSplitCandidate e
      return ()
    if isMorallyIff e then
      addSplitCandidate e
      return ()
    if (← getConfig).splitMatch then
      if (← isMatcherApp e) then
        if let .reduced _ ← reduceMatcher? e then
          -- When instantiating `match`-equations, we add `match`-applications that can be reduced,
          -- and consequently don't need to be split.
          return ()
        else
          addSplitCandidate e
          return ()
    let .const declName _  := e.getAppFn | return ()
      if forbiddenSplitTypes.contains declName then
        return ()
      unless (← isInductivePredicate declName) do
        return ()
      if (← get).split.casesTypes.isSplit declName then
        addSplitCandidate e
      else if (← getConfig).splitIndPred then
        addSplitCandidate e
  | .fvar .. =>
    let .const declName _ := (← whnfD (← inferType e)).getAppFn | return ()
    if (← get).split.casesTypes.isSplit declName then
      addSplitCandidate e
  | _ => pure ()

/--
If `e` is a `cast`-like term (e.g., `cast h a`), add `HEq e a` to the to-do list.
It could be an E-matching theorem, but we want to ensure it is always applied since
we want to rely on the fact that `cast h a` and `a` are in the same equivalence class.
-/
private def pushCastHEqs (e : Expr) : GoalM Unit := do
  match_expr e with
  | f@cast α β h a => pushHEq e a (mkApp4 (mkConst ``cast_heq f.constLevels!) α β h a)
  | f@Eq.rec α a motive v b h => pushHEq e v (mkApp6 (mkConst ``Grind.eqRec_heq f.constLevels!) α a motive v b h)
  | f@Eq.ndrec α a motive v b h => pushHEq e v (mkApp6 (mkConst ``Grind.eqNDRec_heq f.constLevels!) α a motive v b h)
  | f@Eq.recOn α a motive b h v => pushHEq e v (mkApp6 (mkConst ``Grind.eqRecOn_heq f.constLevels!) α a motive b h v)
  | _ => return ()

private def preprocessGroundPattern (e : Expr) : GoalM Expr := do
  shareCommon (← canon (← normalizeLevels (← eraseIrrelevantMData (← unfoldReducible e))))

private def mkENode' (e : Expr) (generation : Nat) : GoalM Unit :=
  mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)

/-- Internalizes the nested ground terms in the given pattern. -/
private partial def internalizePattern (pattern : Expr) (generation : Nat) : GoalM Expr := do
  -- Recall that it is important to ensure patterns are maximally shared since
  -- we assume that in functions such as `getAppsOf` in `EMatch.lean`
  go (← shareCommon pattern)
where
  go (pattern : Expr) : GoalM Expr := do
    if pattern.isBVar || isPatternDontCare pattern then
      return pattern
    else if let some e := groundPattern? pattern then
      let e ← preprocessGroundPattern e
      internalize e generation none
      return mkGroundPattern e
    else pattern.withApp fun f args => do
      return mkAppN f (← args.mapM go)

/-- Internalizes the `MatchCond` gadget. -/
private def internalizeMatchCond (matchCond : Expr) (generation : Nat) : GoalM Unit := do
  mkENode' matchCond generation
  let (lhss, e') ← collectMatchCondLhssAndAbstract matchCond
  lhss.forM fun lhs => do internalize lhs generation; registerParent matchCond lhs
  propagateUp matchCond
  internalize e' generation
  trace_goal[grind.debug.matchCond.lambda] "(idx := {(← getENode e'.getAppFn).idx}) {e'.getAppFn}"
  trace_goal[grind.debug.matchCond.lambda] "auxiliary application{indentExpr e'}"
  pushEq matchCond e' (← mkEqRefl matchCond)

def activateTheorem (thm : EMatchTheorem) (generation : Nat) : GoalM Unit := do
  -- Recall that we use the proof as part of the key for a set of instances found so far.
  -- We don't want to use structural equality when comparing keys.
  let proof ← shareCommon thm.proof
  let thm := { thm with proof, patterns := (← thm.patterns.mapM (internalizePattern · generation)) }
  trace_goal[grind.ematch] "activated `{thm.origin.key}`, {thm.patterns.map ppPattern}"
  modify fun s => { s with ematch.newThms := s.ematch.newThms.push thm }

/--
If `Config.matchEqs` is set to `true`, and `f` is `match`-auxiliary function,
adds its equations to `newThms`.
-/
private def addMatchEqns (f : Expr) (generation : Nat) : GoalM Unit := do
  if !(← getConfig).matchEqs then return ()
  let .const declName _ := f | return ()
  if !(← isMatcher declName) then return ()
  if (← get).ematch.matchEqNames.contains declName then return ()
  modify fun s => { s with ematch.matchEqNames := s.ematch.matchEqNames.insert declName }
  for eqn in (← Match.getEquationsFor declName).eqnNames do
    -- We disable pattern normalization to prevent the `match`-expression to be reduced.
    activateTheorem (← mkEMatchEqTheorem eqn (normalizePattern := false)) generation

private def activateTheoremPatterns (fName : Name) (generation : Nat) : GoalM Unit := do
  if let some (thms, thmMap) := (← get).ematch.thmMap.retrieve? fName then
    modify fun s => { s with ematch.thmMap := thmMap }
    let appMap := (← get).appMap
    for thm in thms do
      unless (← get).ematch.thmMap.isErased thm.origin do
        let symbols := thm.symbols.filter fun sym => !appMap.contains sym
        let thm := { thm with symbols }
        match symbols with
        | [] => activateTheorem thm generation
        | _ =>
          trace_goal[grind.ematch] "reinsert `{thm.origin.key}`"
          modify fun s => { s with ematch.thmMap := s.ematch.thmMap.insert thm }

/--
If type of `a` is an inductive datatype with one constructor `ctor` without fields,
pushes the equality `a = ctor`.

Remark: we added this feature because `isDefEq` implements it, and consequently
the simplifier reduces terms of the form `a = ctor` to `True` using `eq_self`.
This `isDefEq` feature was negatively affecting `grind` until we added an
equivalent one here. For example, when splitting on a `match`-expression
using Unit-like types, equalites about these types were being reduced to `True`
by `simp` (i.e., in the `grind` preprocessor), and `grind` would never see
these facts.
-/
private def propagateUnitLike (a : Expr) (generation : Nat) : GoalM Unit := do
  let aType ← whnfD (← inferType a)
  matchConstStructureLike aType.getAppFn (fun _ => return ()) fun inductVal us ctorVal => do
    unless a.isAppOf ctorVal.name do
      if ctorVal.numFields == 0 then
        let params := aType.getAppArgs[:inductVal.numParams]
        let unit := mkAppN (mkConst ctorVal.name us) params
        let unit ← shareCommon unit
        internalize unit generation
        pushEq a unit <| (← mkEqRefl unit)

@[export lean_grind_internalize]
private partial def internalizeImpl (e : Expr) (generation : Nat) (parent? : Option Expr := none) : GoalM Unit := withIncRecDepth do
  if (← alreadyInternalized e) then
    trace_goal[grind.debug.internalize] "already internalized: {e}"
    /-
    Even if `e` has already been internalized, we must check whether it has also been internalized in
    the satellite solvers. For example, suppose we have already internalized the term `f (a + 1)`.
    The `1` in this term is treated as an offset for the offset term `a + 1` by the arithmetic module, and
    only nodes for `a` and `a+1` are created. However, an ENode for `1` is created here.
    Later, if we try to internalize `f 1`, the arithmetic module must create a node for `1`.
    Otherwise, it will not be able to propagate that `a + 1 = 1` when `a = 0`
    -/
    Arith.internalize e parent?
    return ()
  trace_goal[grind.internalize] "{e}"
  propagateUnitLike e generation
  match e with
  | .bvar .. => unreachable!
  | .sort .. => return ()
  | .fvar .. =>
    mkENode' e generation
    checkAndAddSplitCandidate e
  | .letE .. | .lam .. =>
    mkENode' e generation
  | .forallE _ d b _ =>
    mkENode' e generation
    if (← isProp d <&&> isProp e) then
      internalizeImpl d generation e
      registerParent e d
      unless b.hasLooseBVars do
        internalizeImpl b generation e
        registerParent e b
      propagateUp e
  | .lit .. =>
    mkENode e generation
  | .const declName _ =>
    mkENode e generation
    activateTheoremPatterns declName generation
  | .mvar .. =>
    reportIssue! "unexpected metavariable during internalization{indentExpr e}\n`grind` is not supposed to be used in goals containing metavariables."
    mkENode' e generation
  | .mdata .. =>
    reportIssue! "unexpected metadata found during internalization{indentExpr e}\n`grind` uses a pre-processing step that eliminates metadata"
    mkENode' e generation
  | .proj .. =>
    reportIssue! "unexpected kernel projection term during internalization{indentExpr e}\n`grind` uses a pre-processing step that folds them as projection applications, the pre-processor should have failed to fold this term"
    mkENode' e generation
  | .app .. =>
    if (← isLitValue e) then
      -- We do not want to internalize the components of a literal value.
      mkENode e generation
      Arith.internalize e parent?
    else if e.isAppOfArity ``Grind.MatchCond 1 then
      internalizeMatchCond e generation
    else e.withApp fun f args => do
      mkENode e generation
      checkAndAddSplitCandidate e
      pushCastHEqs e
      addMatchEqns f generation
      if f.isConstOf ``Lean.Grind.nestedProof && args.size == 2 then
        -- We only internalize the proposition. We can skip the proof because of
        -- proof irrelevance
        let c := args[0]!
        internalizeImpl c generation e
        registerParent e c
      else if f.isConstOf ``ite && args.size == 5 then
        let c := args[1]!
        internalizeImpl c generation e
        registerParent e c
      else
        if let .const fName _ := f then
          activateTheoremPatterns fName generation
        else
          internalizeImpl f generation e
        registerParent e f
        for h : i in [: args.size] do
          let arg := args[i]
          internalize arg generation e
          registerParent e arg
      addCongrTable e
      updateAppMap e
      Arith.internalize e parent?
      propagateUp e
      propagateBetaForNewApp e

end Lean.Meta.Grind
