/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Util
public import Init.Grind.Lemmas
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Lean.Meta.LitValues
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.Match.MatchEqs
import Lean.Util.CollectLevelParams
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Beta
import Lean.Meta.Tactic.Grind.MatchCond
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
public section
namespace Lean.Meta.Grind

/-- Adds `e` to congruence table. -/
def addCongrTable (e : Expr) : GoalM Unit := do
  if let some { e := e' } := (← get).congrTable.find? { e } then
    -- `f` and `g` must have the same type.
    -- See paper: Congruence Closure in Intensional Type Theory
    if e.isApp then
      let f := e.getAppFn
      let g := e'.getAppFn
      unless isSameExpr f g do
        unless (← hasSameType f g) do
          reportIssue! "found congruence between{indentExpr e}\nand{indentExpr e'}\nbut functions have different types"
          return ()
    trace_goal[grind.debug.congr] "{e} = {e'}"
    pushEqHEq e e' congrPlaceholderProof
    if (← swapCgrRepr e e') then
      /-
      Recall that `isDiseq` and `mkDiseqProof?` are implemented using the the congruence table.
      So, if `e` is an equality `a = b`, and is the equivalence class of `False`, but `e'` is not,
      we **must** make `e` the representative of the congruence class.
      The equivalence classes of `e` and `e'` will be merged eventually since we used `pushEqHEq` above,
      but assume that a conflict is detected before we merge the equivalence classes of `e` and `e'`,
      and we try to construct a proof that uses the fact that `a ≠ b`. To retrieve this disequality
      we must ensure that `e` is still the congruence root.
      -/
      modify fun s => { s with congrTable := s.congrTable.insert { e } }
      setENode e' { (← getENode e') with congr := e }
      setENode e { (← getENode e) with congr := e }
    else
      let node ← getENode e
      setENode e { node with congr := e' }
  else
    modify fun s => { s with congrTable := s.congrTable.insert { e } }
where
  swapCgrRepr (e e' : Expr) : GoalM Bool := do
    let_expr Eq _ _ _ := e | return false
    unless (← isEqFalse e) do return false
    return !(← isEqFalse e')

/--
Given an application `e` of the form `f a_1 ... a_n`,
adds entry `f ↦ e` to `appMap`. Recall that `appMap` is a multi-map.
-/
private def updateAppMap (e : Expr) : GoalM Unit := do
  let key := e.toHeadIndex
  trace_goal[grind.debug.appMap] "{e} => {repr key}"
  modify fun s => { s with
    appMap := if let some es := s.appMap.find? key then
      s.appMap.insert key (e :: es)
    else
      s.appMap.insert key [e]
  }
  saveAppOf key

private def forbiddenSplitTypes := [``Eq, ``HEq, ``True, ``False]

/-- Returns `true` if `e` is of the form `@Eq Prop a b` -/
def isMorallyIff (e : Expr) : Bool :=
  let_expr Eq α _ _ := e | false
  α.isProp

private def mkDefaultSplitInfo (e : Expr) : GrindM SplitInfo :=
  return .default e (← readThe Context).splitSource

private def addDefaultSplitCandidate (e : Expr) : GoalM Unit := do
  addSplitCandidate (← mkDefaultSplitInfo e)

/-- Inserts `e` into the list of case-split candidates if applicable. -/
private def checkAndAddSplitCandidate (e : Expr) : GoalM Unit := do
  match h : e with
  | .app .. =>
    if (← getConfig).splitIte && (isIte e || isDIte e) then
      addDefaultSplitCandidate e
      return ()
    if isMorallyIff e then
      addDefaultSplitCandidate e
      return ()
    if (← getConfig).splitMatch then
      if (← isMatcherApp e) then
        if let .reduced _ ← reduceMatcher? e then
          -- When instantiating `match`-equations, we add `match`-applications that can be reduced,
          -- and consequently don't need to be split.
          return ()
        else
          addDefaultSplitCandidate e
          return ()
    let .const declName _  := e.getAppFn | return ()
      if forbiddenSplitTypes.contains declName then
        return ()
      unless (← isInductivePredicate declName) do
        return ()
      if (← get).split.casesTypes.isSplit declName then
        addDefaultSplitCandidate e
      else if (← getConfig).splitIndPred then
        addDefaultSplitCandidate e
  | .fvar .. =>
    let .const declName _ := (← whnf (← inferType e)).getAppFn | return ()
    if (← get).split.casesTypes.isSplit declName then
      addDefaultSplitCandidate e
  | .forallE _ d _ _ =>
    let currSplitSource := (← readThe Context).splitSource
    if (← getConfig).splitImp then
      if (← isProp d) then
        addSplitCandidate (.imp e (h ▸ rfl) currSplitSource)
    else if Arith.isRelevantPred d then
      -- TODO: should we keep lookahead after we implement non-chronological backtracking?
      if (← getConfig).lookahead then
        addLookaheadCandidate (.imp e (h ▸ rfl) currSplitSource)
      -- We used to add the `split` only if `lookahead := false`, but it was counterintuitive
      -- to make `grind` "stronger" by disabling a feature.
      addSplitCandidate (.imp e (h ▸ rfl) currSplitSource)
  | _ => pure ()

/--
If `e` is a `cast`-like term (e.g., `cast h a`), add `e ≍ a` to the to-do list.
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

private def mkENode' (e : Expr) (generation : Nat) : GoalM Unit :=
  mkENodeCore e (ctor := false) (interpreted := false) (generation := generation)

/-- Internalizes the nested ground terms in the given pattern. -/
private partial def internalizePattern (pattern : Expr) (generation : Nat) (origin : Origin) : GoalM Expr := do
  -- Recall that it is important to ensure patterns are maximally shared since
  -- we assume that in functions such as `getAppsOf` in `EMatch.lean`
  go (← shareCommon pattern)
where
  go (pattern : Expr) : GoalM Expr := do
    if pattern.isBVar || isPatternDontCare pattern then
      return pattern
    else if let some e := groundPattern? pattern then
      let e ← preprocessLight e
      let e ← if e.hasLevelParam && origin matches .decl _ then
        /-
        If `e` has universe parameters and it is **not** local. That is,
        it contains the universe parameters of some global theorem.
        Then, we convert `e`'s universe parameters into universe meta-variables.
        Remark: it is pointless to internalize the result because it contains these helper meta-variables.
        Remark: universe polymorphic ground patterns are not common, but they do occur in the
        core library.
        -/
        let ps := collectLevelParams {} e |>.params
        let us ← ps.mapM fun _ => mkFreshLevelMVar
        pure <| e.instantiateLevelParamsArray ps us
      else
        internalize e generation none
        pure e
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
  internalizeSimpleMatchCondImp
where
  /--
  We say `MatchCond` is simple if its argument is an implication such as `x = 0 -> ...`
  If that is the case, we also internalize the implication to ensure grind can split on the antecedents.
  We added this extra case to make sure the user is not surprised by `grind` failing at
  ```
  example (x y : Nat)
      : 0 < match x, y with
            | 0, 0   => 1
            | _, _ => x + y := by -- x or y must be greater than 0
    grind
  ```
  We should try to find a better and more general approach for handling the example above.
  -/
  internalizeSimpleMatchCondImp : GoalM Unit := do
    let_expr Grind.MatchCond e := matchCond | return ()
    let .forallE _ d b _ := e | return ()
    if b.hasLooseBVars then return ()
    if (← isProp d) then
      internalize e generation
    pushEq matchCond e (← mkEqRefl matchCond)

def activateTheorem (thm : EMatchTheorem) (generation : Nat) : GoalM Unit := do
  -- Recall that we use the proof as part of the key for a set of instances found so far.
  -- We don't want to use structural equality when comparing keys.
  let proof ← shareCommon thm.proof
  let thm := { thm with proof, patterns := (← thm.patterns.mapM (internalizePattern · generation thm.origin)) }
  trace_goal[grind.ematch] "activated `{thm.origin.pp}`, {thm.patterns.map ppPattern}"
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
  -- for eqn in (← Match.getEquationsFor declName).eqnNames do
  for eqn in (← Match.genMatchCongrEqns declName) do
    -- We disable pattern normalization to prevent the `match`-expression to be reduced.
    activateTheorem (← mkEMatchEqTheorem eqn (normalizePattern := false)) generation

@[specialize]
private def activateTheorems [TheoremLike α] (declName : Name)
    (getThms : GoalM (Theorems α))
    (setThms : Theorems α → GoalM Unit)
    (reinsertThm : α → GoalM Unit)
    (activateThm : α → GoalM Unit) : GoalM Unit := do
  if let some (thms, s) := (← getThms).retrieve? declName then
    setThms s
    for thm in thms do
      let origin := TheoremLike.getOrigin thm
      trace_goal[grind.debug.theorem.activate] "`{declName}` => `{origin.key}`"
      unless s.isErased origin do
        let appMap  := (← get).appMap
        let symbols := TheoremLike.getSymbols thm
        let symbols := symbols.filter fun sym => !appMap.contains sym
        let thm     := TheoremLike.setSymbols thm symbols
        match symbols with
        | [] =>
          trace_goal[grind.debug.theorem.activate] "`{origin.key}`"
          activateThm thm
        | _ =>
          trace_goal[grind.debug.theorem.activate] "reinsert `{origin.key}`"
          reinsertThm thm

private def activateTheoremPatterns (fName : Name) (generation : Nat) : GoalM Unit := do
  activateTheorems fName (return (← get).ematch.thmMap)
    (fun thmMap => modify fun s => { s with ematch.thmMap := thmMap })
    (fun thm => modify fun s => { s with ematch.thmMap := s.ematch.thmMap.insert thm })
    (fun thm => activateTheorem thm generation)

/--
If type of `a` is a structure and is tagged with `[grind ext]` attribute,
propagate `a = ⟨a.1, ..., a.n⟩`

This function subsumes the `propagateUnitLike` function we used in the past.
Recall that the `propagateUnitLike` was added because `isDefEq` implements it,
and consequently the simplifier reduces terms of the form `a = ctor` to `True` using `eq_self`.
This `isDefEq` feature was negatively affecting `grind` until we added an
equivalent one here. For example, when splitting on a `match`-expression
using Unit-like types, equalities about these types were being reduced to `True`
by `simp` (i.e., in the `grind` preprocessor), and `grind` would never see
these facts.
-/
private def propagateEtaStruct (a : Expr) (generation : Nat) : GoalM Unit := do
  unless (← getConfig).etaStruct do return ()
  let aType ← whnf (← inferType a)
  matchConstStructureLike aType.getAppFn (fun _ => return ()) fun inductVal us ctorVal => do
    unless a.isAppOf ctorVal.name do
      -- TODO: remove ctorVal.numFields after update stage0
      if (← isExtTheorem inductVal.name) || ctorVal.numFields == 0 then
        let params := aType.getAppArgs[*...inductVal.numParams]
        let mut ctorApp := mkAppN (mkConst ctorVal.name us) params
        for j in *...ctorVal.numFields do
          let mut proj ← mkProjFn ctorVal us params j a
          if (← isProof proj) then
            proj ← markProof proj
          ctorApp := mkApp ctorApp proj
        ctorApp ← preprocessLight ctorApp
        internalize ctorApp generation
        let u ← getLevel aType
        let expectedProp := mkApp3 (mkConst ``Eq [u]) aType a ctorApp
        pushEq a ctorApp <| mkExpectedPropHint (mkApp2 (mkConst ``Eq.refl [u]) aType a) expectedProp

/-- Returns `true` if we can ignore `ext` for functions occurring as arguments of a `declName`-application. -/
private def extParentsToIgnore (declName : Name) : Bool :=
  declName == ``Eq || declName == ``HEq || declName == ``dite || declName == ``ite
  || declName == ``Exists || declName == ``Subtype

/--
Given a term `arg` that occurs as the argument at position `i` of an `f`-application `parent?`,
we consider `arg` as a candidate for case-splitting. For every other argument `arg'` that also appears
at position `i` in an `f`-application and has the same type as `e`, we add the case-split candidate `arg = arg'`.

When performing the case split, we consider the following two cases:
- `arg = arg'`, which may introduce a new congruence between the corresponding `f`-applications.
- `¬(arg = arg')`, which may trigger extensionality theorems for the type of `arg`.

This feature enables `grind` to solve examples such as:
```lean
example (f : (Nat → Nat) → Nat) : a = b → f (fun x => a + x) = f (fun x => b + x) := by
  grind
```
-/
private def addSplitCandidatesForExt (arg : Expr) (generation : Nat) (parent? : Option Expr := none) : GoalM Unit := do
  let some parent := parent? | return ()
  unless parent.isApp do return ()
  let f := parent.getAppFn
  if let .const declName _ := f then
    if extParentsToIgnore declName then return ()
  let type ← inferType arg
  -- Remark: we currently do not perform function extensionality on functions that produce a type that is not a proposition.
  -- We may add an option to enable that in the future.
  let u? ← typeFormerTypeLevel type
  if u? != .none && u? != some .zero then return ()
  let mut i  := parent.getAppNumArgs
  let mut it := parent
  repeat
    if !it.isApp then return ()
    i := i - 1
    if isSameExpr arg it.appArg! then
      found f i type parent
    it := it.appFn!
where
  found (f : Expr) (i : Nat) (type : Expr) (parent : Expr) : GoalM Unit := do
    trace_goal[grind.debug.ext] "{f}, {i}, {arg}"
    let others := (← get).split.argsAt.find? (f, i) |>.getD []
    for other in others do
      if (← isDefEqD type other.type) then
        let eq := mkApp3 (mkConst ``Eq [← getLevel type]) type arg other.arg
        let eq ← shareCommon eq
        internalize eq generation
        trace_goal[grind.ext.candidate] "{eq}"
        -- We do not use lookahead here because it is too incomplete.
        -- if (← getConfig).lookahead then
        --   addLookaheadCandidate (.arg other.app parent i eq)
        -- else
        let currSplitSource := (← readThe Context).splitSource
        addSplitCandidate (.arg other.app parent i eq currSplitSource)
    modify fun s => { s with split.argsAt := s.split.argsAt.insert (f, i) ({ arg, type, app := parent } :: others) }
    return ()

/-- Applies `addSplitCandidatesForExt` if `funext` is enabled. -/
private def addSplitCandidatesForFunext (arg : Expr) (generation : Nat) (parent? : Option Expr := none) : GoalM Unit := do
  unless (← getConfig).funext do return ()
  addSplitCandidatesForExt arg generation parent?

/--
Tries to eta-reduce the given expression.
If successful, pushes a new equality between the two terms.
-/
private def tryEta (e : Expr) (generation : Nat) : GoalM Unit := do
  let e' := e.eta
  if e != e' then
    let e' ← shareCommon e'
    internalize e' generation
    pushEq e e' (← mkEqRefl e)

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
    Solvers.internalize e parent?
  else
    go
    propagateEtaStruct e generation
where
  go : GoalM Unit := do
    trace_goal[grind.internalize] "[{generation}] {e}"
    match e with
    | .bvar .. => unreachable!
    | .sort .. =>
      /-
      **Note**: It may seem wasteful to create ENodes for sorts, but it is useful for the E-matching module.
      The E-matching module assumes that the arguments of an internalized application have also been internalized,
      unless they are `grind` gadgets.
      -/
      mkENode' e generation
    | .fvar .. =>
      mkENode' e generation
      checkAndAddSplitCandidate e
    | .letE .. =>
      mkENode' e generation
    | .lam .. =>
      addSplitCandidatesForFunext e generation parent?
      mkENode' e generation
      tryEta e generation
    | .forallE _ d b _ =>
      mkENode' e generation
      internalizeImpl d generation e
      registerParent e d
      unless b.hasLooseBVars do
        internalizeImpl b generation e
        registerParent e b
        addCongrTable e
      if (← isProp d <&&> isProp e) then
        propagateUp e
        checkAndAddSplitCandidate e
    | .lit .. =>
      mkENode e generation
    | .const declName _ =>
      mkENode e generation
      activateTheoremPatterns declName generation
    | .mvar .. =>
      if (← reportMVarInternalization) then
        reportIssue! "unexpected metavariable during internalization{indentExpr e}\n`grind` is not supposed to be used in goals containing metavariables."
      mkENode' e generation
    | .mdata .. =>
      reportIssue! "unexpected metadata found during internalization{indentExpr e}\n`grind` uses a pre-processing step that eliminates metadata"
      mkENode' e generation
    | .proj .. =>
      reportIssue! "unexpected kernel projection term during internalization{indentExpr e}\n`grind` uses a pre-processing step that folds them as projection applications, the pre-processor failed to fold this term"
      mkENode' e generation
    | .app .. =>
      if (← isLitValue e) then
        -- We do not want to internalize the components of a literal value.
        mkENode e generation
        Solvers.internalize e parent?
      else if e.isAppOfArity ``Grind.MatchCond 1 then
        internalizeMatchCond e generation
      else e.withApp fun f args => do
        mkENode e generation
        updateAppMap e
        checkAndAddSplitCandidate e
        pushCastHEqs e
        addMatchEqns f generation
        if args.size == 2 && f.isConstOf ``Grind.nestedProof then
          -- We only internalize the proposition. We can skip the proof because of
          -- proof irrelevance
          let c := args[0]!
          internalizeImpl c generation e
          registerParent e c
          pushEqTrue c <| mkApp2 (mkConst ``eq_true) c args[1]!
        else if args.size == 2 && f.isConstOf ``Grind.nestedDecidable then
          -- We only internalize the proposition. We can skip the instance because it is
          -- a subsingleton
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
          for h : i in *...args.size do
            let arg := args[i]
            internalize arg generation e
            registerParent e arg
        addCongrTable e
        Solvers.internalize e parent?
        propagateUp e
        propagateBetaForNewApp e

end Lean.Meta.Grind
