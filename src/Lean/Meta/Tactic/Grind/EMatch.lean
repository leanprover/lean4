/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Util.CollectLevelMVars
import Lean.Meta.Tactic.Grind.Core
import Lean.Meta.Tactic.Grind.MatchDiscrOnly
import Lean.Meta.Tactic.Grind.ProveEq
import Lean.Meta.Tactic.Grind.SynthInstance
import Lean.Meta.Tactic.Grind.Simp
public section
namespace Lean.Meta.Grind
namespace EMatch
/-! This module implements a simple E-matching procedure as a backtracking search. -/

/-- We represent an `E-matching` problem as a list of constraints. -/
inductive Cnstr where
  | /-- Matches pattern `pat` with term `e` -/
    «match» (gen? : Option GenPatternInfo) (pat : Expr) (e : Expr)
  | /-- Matches offset pattern `pat+k` with term `e` -/
    offset (gen? : Option GenPatternInfo) (pat : Expr) (k : Nat) (e : Expr)
  | /-- This constraint is used to encode multi-patterns. -/
    «continue» (pat : Expr)
  deriving Inhabited

/--
Internal "marker" for representing unassigned elements in the `assignment` field.
This is a small hack to avoid one extra level of indirection by using `Option Expr` at `assignment`.
-/
private def unassigned : Expr := mkConst (Name.mkSimple "[grind_unassigned]")

/--
Internal "marker" for representing equality proofs for generalized patterns.
They must be synthesized after we have the partial assignment.
-/
private def delayedEqProof : Expr := mkConst (Name.mkSimple "[grind_delayed_eq_proof]")

private def assignmentToMessageData (assignment : Array Expr) : Array MessageData :=
  assignment.reverse.map fun e =>
    if isSameExpr e unassigned then m!"_" else m!"{e}"

/--
Choice point for the backtracking search.
The state of the procedure contains a stack of choices.
-/
structure Choice where
  /-- Constraints to be processed. -/
  cnstrs     : List Cnstr
  /-- Maximum term generation found so far. -/
  gen        : Nat
  /-- Partial assignment so far. Recall that pattern variables are encoded as de-Bruijn variables. -/
  assignment : Array Expr
  deriving Inhabited

/-- Context for the E-matching monad. -/
structure Context where
  /-- `useMT` is `true` if we are using the mod-time optimization. It is always set to false for new `EMatchTheorem`s. -/
  useMT : Bool := true
  /-- `EMatchTheorem` being processed. -/
  thm   : EMatchTheorem := default
  /-- Initial application used to start E-matching -/
  initApp : Expr := default
  deriving Inhabited

/-- State for the E-matching monad -/
structure SearchState where
  /-- Choices that still have to be processed. -/
  choiceStack  : List Choice := []
  deriving Inhabited

abbrev M := ReaderT Context $ StateRefT SearchState GoalM

def M.run' (x : M α) : GoalM α :=
  x {} |>.run' {}

@[inline] private abbrev withInitApp (e : Expr) (x : M α) : M α :=
  withReader (fun ctx => { ctx with initApp := e }) x

/--
Assigns `bidx := e` in `c`. If `bidx` is already assigned in `c`, we check whether
`e` and `c.assignment[bidx]` are in the same equivalence class.
This function assumes `bidx < c.assignment.size`.
Recall that we initialize the assignment array with the number of theorem parameters.
-/
private def assign? (c : Choice) (bidx : Nat) (e : Expr) : OptionT GoalM Choice := do
  if h : bidx < c.assignment.size then
    let v := c.assignment[bidx]
    if isSameExpr v unassigned then
      return { c with assignment := c.assignment.set bidx e }
    else
      guard (← isEqv v e)
      return c
  else
    -- `Choice` was not properly initialized
    unreachable!

/--
Assigns `bidx` with the marker for a delayed equality proof for generalized patterns.
The proof is assigned after we have the complete assignment.
-/
private def assignDelayedEqProof? (c : Choice) (bidx : Nat) : OptionT GoalM Choice := do
  if h : bidx < c.assignment.size then
    let v := c.assignment[bidx]
    if isSameExpr v unassigned then
      return { c with assignment := c.assignment.set bidx delayedEqProof }
    else
      return c
  else
    -- `Choice` was not properly initialized
    unreachable!


private def unassign (c : Choice) (bidx : Nat) : Choice :=
  { c with assignment := c.assignment.set! bidx unassigned }

/--
Returns `true` if the function `pFn` of a pattern is equivalent to the function `eFn`.
Recall that we ignore universe levels in patterns.
-/
private def eqvFunctions (pFn eFn : Expr) : Bool :=
  (pFn.isFVar && pFn == eFn)
  || (pFn.isConst && eFn.isConstOf pFn.constName!)

protected def _root_.Lean.Meta.Grind.GenPatternInfo.assign? (genInfo : GenPatternInfo) (c : Choice) (x : Expr) : OptionT GoalM Choice := do
  let c ← assign? c genInfo.xIdx x
  let c ← assignDelayedEqProof? c genInfo.hIdx
  return c

private def matchGroundPattern (pArg eArg : Expr) : GoalM Bool := do
  /-
  1) Remark:
  We need to use `withReducibleAndInstances` because ground patterns are often instances.
  Here is an example
  ```
  instance : Max Nat where
    max := Nat.max -- Redefined the instance

  example (a : Nat) : max a a = a := by
    grind
  ```
  Possible future improvements:
  - When `diagnostics` is true, try with `withDefault` and report issue if it succeeds.
  - (minor) Only use `withReducibleAndInstances` if the argument is an implicit instance.
    Potential issue: some user write `{_ : Class α}` when the instance can be inferred from
    explicit arguments.
  2) Remark:
  If `pArg` contains universe metavariables, we use `withoutModifyingMCtx` to ensure the metavariables
  are not assigned. These universe metavariables are created at `internalizePattern` for universe polymorphic
  ground patterns. They are not common, but they occur in practice.
  -/
  if pArg.hasLevelMVar then
    withoutModifyingMCtx <| withReducibleAndInstances <| isDefEq pArg eArg
  else
    isEqv pArg eArg <||> withReducibleAndInstances (isDefEq pArg eArg)

/-- Matches a pattern argument. See `matchArgs?`. -/
private def matchArg? (c : Choice) (pArg : Expr) (eArg : Expr) : OptionT GoalM Choice := do
  if isPatternDontCare pArg then
    return c
  else if pArg.isBVar then
    assign? c pArg.bvarIdx! eArg
  else if let some pArg := groundPattern? pArg then
    guard (← matchGroundPattern pArg eArg)
    return c
  else if let some (pArg, k) := isOffsetPattern? pArg then
    assert! Option.isNone <| isOffsetPattern? pArg
    assert! !isPatternDontCare pArg
    return { c with cnstrs := .offset none pArg k eArg :: c.cnstrs }
  else if let some (genInfo, pArg) := isGenPattern? pArg then
    if pArg.isBVar then
      let c ← assign? c pArg.bvarIdx! eArg
      genInfo.assign? c eArg
    else if let some pArg := groundPattern? pArg then
      guard (← matchGroundPattern pArg eArg)
      genInfo.assign? c eArg
    else if let some (pArg, k) := isOffsetPattern? pArg then
      return { c with cnstrs := .offset (some genInfo) pArg k eArg :: c.cnstrs }
    else
      return { c with cnstrs := .match (some genInfo) pArg eArg :: c.cnstrs }
  else
    return { c with cnstrs := .match none pArg eArg :: c.cnstrs }

private def Choice.updateGen (c : Choice) (gen : Nat) : Choice :=
  { c with gen := Nat.max gen c.gen }

private def pushChoice (c : Choice) : M Unit :=
  modify fun s => { s with choiceStack := c :: s.choiceStack }

/--
Matches arguments of pattern `p` with term `e`. Returns `some` if successful,
and `none` otherwise. It may update `c`s assignment and list of constraints to be
processed.
-/
private partial def matchArgs? (c : Choice) (p : Expr) (e : Expr) : OptionT GoalM Choice := do
  if !p.isApp then return c -- Done
  let pArg := p.appArg!
  let eArg := e.appArg!
  let c ← matchArg? c pArg eArg
  matchArgs? c p.appFn! e.appFn!

/-- Similar to `matchArgs?` but if `p` has fewer arguments than `e`, we match `p` with a prefix of `e`. -/
private partial def matchArgsPrefix? (c : Choice) (p : Expr) (e : Expr) : OptionT GoalM Choice := do
  let pn := p.getAppNumArgs
  let en := e.getAppNumArgs
  guard (pn <= en)
  if pn == en then
    matchArgs? c p e
  else
    matchArgs? c p (e.getAppPrefix pn)

-- Helper function for `processMatch` and `processGenMatch`
@[inline] private def isCandidate (n : ENode) (pFn : Expr) (pNumArgs : Nat) (maxGeneration : Nat) : Bool :=
    -- Remark: we use `<` because the instance generation is the maximum term generation + 1
    n.generation < maxGeneration
    -- uses heterogeneous equality or is the root of its congruence class
    && (n.heqProofs || n.isCongrRoot)
    && eqvFunctions pFn n.self.getAppFn
    && n.self.getAppNumArgs == pNumArgs

private def assignGenInfo? (genInfo? : Option GenPatternInfo) (c : Choice) (x : Expr) : OptionT GoalM Choice := do
  let some genInfo := genInfo? | return c
  genInfo.assign? c x

/--
Matches pattern `p` with term `e` with respect to choice `c`.
We traverse the equivalence class of `e` looking for applications compatible with `p`.
For each candidate application, we match the arguments and may update `c`s assignments and constraints.
We add the updated choices to the choice stack.
-/
private partial def processMatch (c : Choice) (genInfo? : Option GenPatternInfo) (p : Expr) (e : Expr) : M Unit := do
  let maxGeneration ← getMaxGeneration
  let pFn := p.getAppFn
  let numArgs := p.getAppNumArgs
  let mut curr := e
  repeat
    let n ← getENode curr
    -- Remark: we use `<` because the instance generation is the maximum term generation + 1
    if isCandidate n pFn numArgs maxGeneration then
      if let some c ← assignGenInfo? genInfo? c e |>.run then
      if let some c ← matchArgs? c p curr |>.run then
        pushChoice (c.updateGen n.generation)
    curr ← getNext curr
    if isSameExpr curr e then break

/--
Matches offset pattern `pArg+k` with term `e` with respect to choice `c`.
-/
private partial def processOffset (c : Choice) (genInfo? : Option GenPatternInfo) (pArg : Expr) (k : Nat) (e : Expr) : M Unit := do
  let maxGeneration ← getMaxGeneration
  let mut curr := e
  repeat
    let n ← getENode curr
    if n.generation < maxGeneration then
      if let some (eArg, k') ← isOffset? curr |>.run then
        if let some c ← assignGenInfo? genInfo? c e |>.run then
          if k' < k then
            let c := c.updateGen n.generation
            pushChoice { c with cnstrs := .offset none pArg (k - k') eArg :: c.cnstrs }
          else if k' == k then
            if let some c ← matchArg? c pArg eArg |>.run then
              pushChoice (c.updateGen n.generation)
          else if k' > k then
            let eArg' := mkNatAdd eArg (mkNatLit (k' - k))
            let eArg' ← shareCommon (← canon eArg')
            internalize eArg' (n.generation+1)
            if let some c ← matchArg? c pArg eArg' |>.run then
              pushChoice (c.updateGen n.generation)
      else if let some k' ← evalNat curr |>.run then
        if let some c ← assignGenInfo? genInfo? c e |>.run then
          if k' >= k then
            let eArg' := mkNatLit (k' - k)
            let eArg' ← shareCommon (← canon eArg')
            internalize eArg' (n.generation+1)
            if let some c ← matchArg? c pArg eArg' |>.run then
              pushChoice (c.updateGen n.generation)
    curr ← getNext curr
    if isSameExpr curr e then break

/--
Returns "applications" in the given goal that may match `p`.
We say "applications," because we assume a constant is a zero-ary application.
-/
private def getAppsOf (p : Expr) : GoalM (Option (List Expr)) := do
  if p.isConst then
    if (← alreadyInternalized p) then
      return some [p]
    else
      return none
  else
    return (← get).appMap.find? p.toHeadIndex

/-- Processes `continue` constraint used to implement multi-patterns. -/
private def processContinue (c : Choice) (p : Expr) : M Unit := do
  let some apps ← getAppsOf p
    | return ()
  let maxGeneration ← getMaxGeneration
  for app in apps do
    let n ← getENode app
    if n.generation < maxGeneration
       && (n.heqProofs || n.isCongrRoot) then
      if let some c ← matchArgsPrefix? c p app |>.run then
        let gen := n.generation
        let c := { c with gen := Nat.max gen c.gen }
        modify fun s => { s with choiceStack := c :: s.choiceStack }

/--
Given a proposition `prop` corresponding to an equational theorem.
Annotate the conditions using `Grind.MatchCond`. See `MatchCond.lean`.
-/
private partial def annotateEqnTypeConds (prop : Expr) (k : Expr → M Expr := pure) : M Expr := do
  if let .forallE n d b bi := prop then
    let d := if (← isProp d) then
      markAsPreMatchCond d
    else
      d
    withLocalDecl n bi d fun x => do
      mkForallFVars #[x] (← annotateEqnTypeConds (b.instantiate1 x) k)
  else
    k prop

/--
Helper function for marking parts of `match`-equation theorem as "do-not-simplify"
`initApp` is the match-expression used to instantiate the `match`-equation.
It also introduce `Grind.MatchCond` at equation conditions. See `MatchCond.lean`.
-/
private def annotateMatchEqnType (prop : Expr) (initApp : Expr) : M Expr := do
  annotateEqnTypeConds prop fun prop => do
    let_expr f@Eq α lhs rhs := prop | return prop
    -- See comment at `Grind.EqMatch`
    let lhs ← markAsSimpMatchDiscrsOnly lhs
    return mkApp4 (mkConst ``Grind.EqMatch f.constLevels!) α lhs rhs initApp

/--
Helper function for collecting constants containing unassigned universe levels.
This functions is used by `assignUnassignedLevelMVars`
-/
private def collectConstsWithLevelMVars (e : Expr) : CoreM (Array Expr) := do
  let (_, s) ← go |>.run {}
  return s.toArray
where
  go : StateRefT (Std.HashSet Expr) CoreM Unit := do
    e.forEach fun e => do
      if e.isConst && e.hasLevelMVar then
        modify (·.insert e)

/--
Helper function for E-match theorems containing universe metavariables that do not occur
in any of their parameters. This is a very rare case, but it does occur in practice.
Example:
```lean
@[simp, grind =] theorem down_pure {φ : Prop} : (⌜φ⌝ : SPred []).down = φ := rfl
```

The parameter `us` contains the unassigned universe metavariables.

Recall that when we collect patterns for a theorem, we check coverage only for regular
parameters, not universe parameters. This function attempts to instantiate the universe
parameters using the following heuristic:

* Collect all constants `C` in `prop` that contain universe metavariables.
* Create a collection `P` of pairs `(c, cs)` where `c ∈ C` and `cs` are instances of `c` in the current goal.
* Sort `P` by the size of `cs`, prioritizing constants with fewer occurrences.
* Perform a backtracking search to unify each `c` with its occurrences. Stop as soon as all universe parameters are instantiated.

We expect this function not to be a performance bottleneck in practice because:

1. Very few theorems contain universe metavariables not covered by any parameters.
2. These theorems usually involve only a small number of universe levels and universe polymorphic constants.
3. Goals rarely contain constants instantiated with many different universe variables.

If this does become a performance issue, we will need to add support for assigning universe levels
during E-matching and check for universe-level coverage when collecting patterns.

The result is a collection of pairs `(proof', prop')` where `proof'` and `prop'` are `proof` and `prop`
with all universe metavariables instantiated.
-/
private def assignUnassignedLevelMVars (us : Array LMVarId) (proof : Expr) (prop : Expr) : GoalM (Array (Expr × Expr)) := do
  let us := us.map mkLevelMVar
  let cs ← collectConstsWithLevelMVars prop
  let mut candidates : Array (Expr × Array Expr) := #[]
  for c in cs do
    let declName := c.constName!
    if let some apps := (← getThe Goal).appMap.find? (.const declName) then
      let consts : Std.HashSet Expr := Std.HashSet.ofList <| apps.map Expr.getAppFn
      candidates := candidates.push (c, consts.toArray)
  candidates := candidates.qsort fun (c₁, cs₁) (c₂, cs₂) =>
    if cs₁.size == cs₂.size then c₁.quickLt c₂ else cs₁.size < cs₂.size
  let rec search (us : Array Level) (i : Nat) : StateRefT (Array (Expr × Expr)) MetaM Unit := do
    checkSystem "grind"
    if h : i < candidates.size then
      let (c, cs) := candidates[i]
      for c' in cs do
        let saved ← getMCtx
        try
          if (← isDefEq c c') then
            -- update pending universe metavariables
            let us ← us.filterMapM fun u => do
              let u ← instantiateLevelMVars u
              if (← hasAssignableLevelMVar u) then
                return some u
              else
                return none
            if us.isEmpty then
              -- all universe metavariables have been assigned
              let prop ← instantiateMVars prop
              let proof ← instantiateMVars proof
              modify (·.push (proof, prop))
              return () -- Found instantiation
            search us (i+1)
        finally
          setMCtx saved
    else
      return ()
  let (_ , s) ← search us 0 |>.run #[]
  return s

private def getUnassignedLevelMVars (e : Expr) : MetaM (Array LMVarId) := do
  unless e.hasLevelMVar do return #[]
  let us := collectLevelMVars {} e |>.result
  us.filterM fun u => isLevelMVarAssignable u

/-- Similar to `reportIssue!`, but only reports issue if `grind.debug` is set to `true` -/
-- **Note**: issues reported by the E-matching module are too distractive. We only
-- report them if `set_option grind.debug true`
macro "reportEMatchIssue!" s:(interpolatedStr(term) <|> term) : doElem => do
  expandReportDbgIssueMacro s.raw

/--
Stores new theorem instance in the state.
Recall that new instances are internalized later, after a full round of ematching.
-/
private def addNewInstance (thm : EMatchTheorem) (proof : Expr) (generation : Nat) : M Unit := do
  let proof ← instantiateMVars proof
  if grind.debug.proofs.get (← getOptions) then
    check proof
  let prop ← inferType proof
  let us ← getUnassignedLevelMVars prop
  if !us.isEmpty then
    let pps ← assignUnassignedLevelMVars us proof prop
    if pps.isEmpty then
      reportEMatchIssue! "failed to instantiate `{thm.origin.pp}`, proposition contains universe metavariables{indentExpr prop}"
      return ()
    for (proof, prop) in pps do
      go proof prop
  else
    go proof prop
where
  go (proof prop : Expr) : M Unit := do
    let mut proof := proof
    let mut prop := prop
    if (← isMatchEqLikeDeclName thm.origin.key) then
      prop ← annotateMatchEqnType prop (← read).initApp
      -- We must add a hint here because `annotateMatchEqnType` introduces `simpMatchDiscrsOnly` and
      -- `Grind.PreMatchCond` which are not reducible.
      proof := mkExpectedPropHint proof prop
    else if (← isEqnThm thm.origin.key) then
      prop ← annotateEqnTypeConds prop
      -- We must add a hint because `annotateEqnTypeConds` introduces `Grind.PreMatchCond`
      -- which is not reducible.
      proof := mkExpectedPropHint proof prop
    trace_goal[grind.ematch.instance] "{thm.origin.pp}: {prop}"
    addTheoremInstance thm proof prop (generation+1)

private def synthesizeInsts (mvars : Array Expr) (bis : Array BinderInfo) : OptionT M Unit := do
  let thm := (← read).thm
  for mvar in mvars, bi in bis do
    if bi.isInstImplicit && !(← mvar.mvarId!.isAssigned) then
      let type ← inferType mvar
      unless (← synthInstanceAndAssign mvar type) do
        reportEMatchIssue! "failed to synthesize instance when instantiating {thm.origin.pp}{indentExpr type}"
        failure

private def preprocessGeneralizedPatternRHS (lhs : Expr) (rhs : Expr) (origin : Origin) (expectedType : Expr) : OptionT (StateT Choice M) Expr := do
  assert! (← alreadyInternalized lhs)
  -- We use `dsimp` here to ensure terms such as `Nat.succ x` are normalized as `x+1`.
  let rhs ← preprocessLight (← dsimpCore rhs)
  internalize rhs (← getGeneration lhs)
  processNewFacts
  if (← isEqv lhs rhs) then
    return rhs
  else
    reportEMatchIssue! "invalid generalized pattern at `{origin.pp}`\nwhen processing argument with type{indentExpr expectedType}\nfailed to prove{indentExpr lhs}\nis equal to{indentExpr rhs}"
    failure

private def assignGeneralizedPatternProof (mvarId : MVarId) (eqProof : Expr) (origin : Origin) : OptionT (StateT Choice M) Unit := do
  unless (← mvarId.checkedAssign eqProof) do
    reportEMatchIssue! "invalid generalized pattern at `{origin.pp}`\nfailed to assign {mkMVar mvarId}\nwith{indentExpr eqProof}"
    failure

/-- Helper function for `applyAssignment. -/
private def processDelayed (mvars : Array Expr) (i : Nat) (h : i < mvars.size) : OptionT (StateT Choice M) Unit := do
  let thm := (← read).thm
  let mvarId := mvars[i].mvarId!
  let mvarIdType ← instantiateMVars (← mvarId.getType)
  match_expr mvarIdType with
  | Eq α lhs rhs =>
    let rhs ← preprocessGeneralizedPatternRHS lhs rhs thm.origin mvarIdType
    assignGeneralizedPatternProof mvarId (← mkEqProof lhs rhs) thm.origin
  | HEq α lhs β rhs =>
    let rhs ← preprocessGeneralizedPatternRHS lhs rhs thm.origin mvarIdType
    assignGeneralizedPatternProof mvarId (← mkHEqProof lhs rhs) thm.origin
  | _ =>
    reportEMatchIssue! "invalid generalized pattern at `{thm.origin.pp}`\nequality type expected{indentExpr mvarIdType}"
    failure

/-- Helper function for `applyAssignment. -/
private def processUnassigned (mvars : Array Expr) (i : Nat) (v : Expr) (h : i < mvars.size) : OptionT (StateT Choice M) Unit := do
  let thm := (← read).thm
  let numParams := thm.numParams
  let bidx := numParams - i - 1
  let mvarId := mvars[i].mvarId!
  let mvarIdType ← mvarId.getType
  let vType ← inferType v
  let rec unassignOrFail : OptionT (StateT Choice M) Unit := do
    /-
    If there is type error and `vType` is a proposition, we can still instantiate the
    theorem by unassigning `v` and using it as an extra hypothesis.
    Here is an example to motivate the unassignment.
    ```
    example (xs : Array Nat) (w : xs.reverse = xs) (j : Nat) (hj : 0 ≤ j) (hj' : j < xs.size / 2)
        : xs[j] = xs[xs.size - 1 - j] := by
      grind
    ```
    Without the unassignment we get a type error while trying to instantiate the theorem
    ```
    theorem getElem_reverse {xs : Array α} {i : Nat} (hi : i < xs.reverse.size) :
      (xs.reverse)[i] = xs[xs.size - 1 - i]'(by simp at hi; omega)
    ```
    The pattern for this theorem is `xs.reverse[i]`. Note that `hi` occurs there as an implicit argument.
    The term `xs[j]` in our goal e-matches the pattern because we have the equality `xs.reverse = xs`.
    However, the implicit proof at `xs[j]` has type `j < xs.size` instead of `j < xs.reverse.size`.
    -/
    if (← isProp vType) then
      modify (unassign · bidx)
    else
      reportEMatchIssue! "type error constructing proof for {thm.origin.pp}\nwhen assigning metavariable {mvars[i]} with {indentExpr v}\n{← mkHasTypeButIsExpectedMsg vType mvarIdType}"
      failure
  if (← isDefEqD mvarIdType vType) then
    unless (← mvarId.checkedAssign v) do unassignOrFail
  else
    if let some heq ← withoutReportingMVarIssues <| proveEq? vType mvarIdType (abstract := true) then
      /-
      Some of the `cast`s will appear inside the `Grind.MatchCond` binders, and
      we want their proofs to be properly wrapped.
      -/
      let heq := mkApp2 (mkConst ``Grind.nestedProof) (← mkEq vType mvarIdType) heq
      let v ← mkAppM ``cast #[heq, v]
      unless (← mvarId.checkedAssign v) do unassignOrFail
    else
      unassignOrFail

private def applyAssignment (mvars : Array Expr) : OptionT (StateT Choice M) Unit := do
  let numParams := (← read).thm.numParams
  let rec go (i : Nat) := do
    if h : i < mvars.size then
      let bidx := numParams - i - 1
      let v := (← get).assignment[bidx]!
      if isSameExpr v delayedEqProof then
        processDelayed mvars i h
      else if !isSameExpr v unassigned then
        processUnassigned mvars i v h
      go (i + 1)
  go 0

/--
Use a fresh name generator for creating internal metavariables for theorem instantiation.
This is technique to ensure the metavariables ids do not depend on operations performed before invoking `grind`.
Without this trick, we experience counterintuitive behavior where small changes affect the metavariable ids, and
consequently the hash code for expressions, and operations such as `qsort` using `Expr.quickLt` in
`assignUnassignedLevelMVars`.
This code is correct because the auxiliary metavariables created during theorem instantiation cannot escape.
-/
private abbrev withFreshNGen (x : M α) : M α := do
  let ngen ← getNGen
  try
    setNGen { namePrefix := `_uniq.grind.ematch, idx := 1 }
    x
  finally
    setNGen ngen

/--
After processing a (multi-)pattern, use the choice assignment to instantiate the proof.
Missing parameters are synthesized using type inference and type class synthesis."
-/
private partial def instantiateTheorem (c : Choice) : M Unit := withDefault do withNewMCtxDepth do withFreshNGen do
  let thm := (← read).thm
  unless (← markTheoremInstance thm.proof c.assignment) do
    return ()
  trace_goal[grind.ematch.instance.assignment] "{thm.origin.pp}: {assignmentToMessageData c.assignment}"
  let proof ← thm.getProofWithFreshMVarLevels
  let numParams := thm.numParams
  assert! c.assignment.size == numParams
  let (mvars, bis, _) ← forallMetaBoundedTelescope (← inferType proof) numParams
  if mvars.size != thm.numParams then
    reportEMatchIssue! "unexpected number of parameters at {thm.origin.pp}"
    return ()
  let (some _, c) ← applyAssignment mvars |>.run c | return ()
  let some _ ← synthesizeInsts mvars bis | return ()
  let proof := mkAppN proof mvars
  if (← mvars.allM (·.mvarId!.isAssigned)) then
    addNewInstance thm proof c.gen
  else
    let mvars ← mvars.filterM fun mvar => return !(← mvar.mvarId!.isAssigned)
    if let some mvarBad ← mvars.findM? fun mvar => return !(← isProof mvar) then
      reportEMatchIssue! "failed to instantiate {thm.origin.pp}, failed to instantiate non propositional argument with type{indentExpr (← inferType mvarBad)}"
    let proof ← mkLambdaFVars (binderInfoForMVars := .default) mvars (← instantiateMVars proof)
    addNewInstance thm proof c.gen

/-- Process choice stack until we don't have more choices to be processed. -/
private def processChoices : M Unit := do
  let maxGeneration ← getMaxGeneration
  while !(← get).choiceStack.isEmpty do
    checkSystem "ematch"
    if (← checkMaxInstancesExceeded) then return ()
    let c ← modifyGet fun s : SearchState => (s.choiceStack.head!, { s with choiceStack := s.choiceStack.tail! })
    if c.gen < maxGeneration then
      match c.cnstrs with
      | [] => instantiateTheorem c
      | .match genInfo? p e :: cnstrs => processMatch { c with cnstrs } genInfo? p e
      | .offset genInfo? p k e :: cnstrs => processOffset { c with cnstrs } genInfo? p k e
      | .continue p :: cnstrs => processContinue { c with cnstrs } p

private def main (p : Expr) (cnstrs : List Cnstr) : M Unit := do
  let some apps ← getAppsOf p
    | return ()
  let numParams  := (← read).thm.numParams
  let assignment := .replicate numParams unassigned
  let useMT      := (← read).useMT
  let gmt        := (← getThe Goal).ematch.gmt
  for app in apps do
    if (← checkMaxInstancesExceeded) then return ()
    let n ← getENode app
    if (n.heqProofs || n.isCongrRoot) &&
       (!useMT || n.mt == gmt) then
      withInitApp app do
        if let some c ← matchArgsPrefix? { cnstrs, assignment, gen := n.generation } p app |>.run then
          modify fun s => { s with choiceStack := [c] }
          processChoices

/--
Entry point for matching `lhs ←= rhs` patterns.
It traverses disequalities `a = b`, and tries to solve two matching problems:
1- match `lhs` with `a` and `rhs` with `b`
2- match `lhs` with `b` and `rhs` with `a`
-/
private def matchEqBwdPat (p : Expr) : M Unit := do
  let_expr Grind.eqBwdPattern pα plhs prhs := p | return ()
  let numParams  := (← read).thm.numParams
  let assignment := .replicate numParams unassigned
  let useMT      := (← read).useMT
  let gmt        := (← getThe Goal).ematch.gmt
  let false      ← getFalseExpr
  let mut curr   := false
  repeat
    if (← checkMaxInstancesExceeded) then return ()
    let n ← getENode curr
    if (n.heqProofs || n.isCongrRoot) &&
       (!useMT || n.mt == gmt) then
      let_expr Eq α lhs rhs := n.self | pure ()
      if let some c₀ ← matchArg? { cnstrs := [], assignment, gen := n.generation } pα α |>.run then
        let go (lhs rhs : Expr) : M Unit := do
          let some c₁ ← matchArg? c₀ plhs lhs |>.run | return ()
          let some c₂ ← matchArg? c₁ prhs rhs |>.run | return ()
          modify fun s => { s with choiceStack := [c₂] }
          processChoices
        go lhs rhs
        go rhs lhs
    if isSameExpr n.next false then return ()
    curr := n.next

def ematchTheorem (thm : EMatchTheorem) : M Unit := do
  if (← checkMaxInstancesExceeded) then return ()
  withReader (fun ctx => { ctx with thm }) do
    let ps := thm.patterns
    match ps, (← read).useMT with
    | [p],   _     => if isEqBwdPattern p then matchEqBwdPat p else main p []
    | p::ps, false => main p (ps.map (.continue ·))
    | _::_,  true  => tryAll ps []
    | _,     _     => unreachable!
where
  /--
  When using the mod-time optimization with multi-patterns,
  we must start ematching at each different pattern. That is,
  if we have `[p₁, p₂, p₃]`, we must execute
  - `main p₁ [.continue p₂, .continue p₃]`
  - `main p₂ [.continue p₁, .continue p₃]`
  - `main p₃ [.continue p₁, .continue p₂]`
  -/
  tryAll (ps : List Expr) (cs : List Cnstr) : M Unit := do
    match ps with
    | []    => return ()
    | p::ps =>
      main p (cs.reverse ++ (ps.map (.continue ·)))
      tryAll ps (.continue p :: cs)

def ematchTheorems (thms : PArray EMatchTheorem) : M Unit := do
  thms.forM ematchTheorem

end EMatch

open EMatch

/-- Performs one round of E-matching, and returns new instances. -/
private def ematchCore : GoalM Unit := do profileitM Exception "grind ematch" (← getOptions) do
  let go (thms newThms : PArray EMatchTheorem) : EMatch.M Unit := do
    withReader (fun ctx => { ctx with useMT := true }) <| ematchTheorems thms
    withReader (fun ctx => { ctx with useMT := false }) <| ematchTheorems newThms
  if (← checkMaxInstancesExceeded <||> checkMaxEmatchExceeded) then
    return ()
  else
    go (← get).ematch.thms (← get).ematch.newThms |>.run'
    modify fun s => { s with
      ematch.thms      := s.ematch.thms ++ s.ematch.newThms
      ematch.newThms   := {}
      ematch.gmt       := s.ematch.gmt + 1
      ematch.num       := s.ematch.num + 1
    }

/-- Performs one round of E-matching, and returns `true` if new instances were generated. -/
def ematch : GoalM Bool := do
  let numInstances := (← get).ematch.numInstances
  ematchCore
  return (← get).ematch.numInstances != numInstances

end Lean.Meta.Grind
