/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Action
public import Lean.Meta.Tactic.Grind.Anchor
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.CasesMatch
import Lean.Meta.Tactic.Grind.Internalize
public section
namespace Lean.Meta.Grind

inductive SplitStatus where
  | resolved
  | notReady
  | ready (numCases : Nat) (isRec := false) (tryPostpone := false)
  deriving Inhabited, BEq, Repr

/-- Given `c`, the condition of an `if-then-else`, check whether we need to case-split on the `if-then-else` or not -/
private def checkIteCondStatus (c : Expr) : GoalM SplitStatus := do
  if (← isEqTrue c <||> isEqFalse c) then
    return .resolved
  else
    return .ready 2

/--
Given `e` of the form `a ∨ b`, check whether we are ready to case-split on `e`.
That is, `e` is `True`, but neither `a` nor `b` is `True`."
-/
private def checkDisjunctStatus (e a b : Expr) : GoalM SplitStatus := do
  if (← isEqTrue e) then
    if (← isEqTrue a <||> isEqTrue b) then
      return .resolved
    else
      return .ready 2
  else if (← isEqFalse e) then
    return .resolved
  else
    return .notReady

/--
Given `e` of the form `a ∧ b`, check whether we are ready to case-split on `e`.
That is, `e` is `False`, but neither `a` nor `b` is `False`.
 -/
private def checkConjunctStatus (e a b : Expr) : GoalM SplitStatus := do
  if (← isEqTrue e) then
    return .resolved
  else if (← isEqFalse e) then
    if (← isEqFalse a <||> isEqFalse b) then
      return .resolved
    else
      return .ready 2
  else
    return .notReady

/--
Given `e` of the form `@Eq Prop a b`, check whether we are ready to case-split on `e`.
There are two cases:
1- `e` is `True`, but neither both `a` and `b` are `True`, nor both `a` and `b` are `False`.
2- `e` is `False`, but neither `a` is `True` and `b` is `False`, nor `a` is `False` and `b` is `True`.
-/
private def checkIffStatus (e a b : Expr) : GoalM SplitStatus := do
  if (← isEqTrue e) then
    if (← (isEqTrue a <&&> isEqTrue b) <||> (isEqFalse a <&&> isEqFalse b)) then
      return .resolved
    else
      return .ready 2
  else if (← isEqFalse e) then
    if (← (isEqTrue a <&&> isEqFalse b) <||> (isEqFalse a <&&> isEqTrue b)) then
      return .resolved
    else
      return .ready 2
  else
    return .notReady

/-- Returns `true` if `c` is congruent to a case-split that was already performed. -/
private def isCongrToPrevSplit (c : Expr) : GoalM Bool := do
  unless c.isApp do return false
  (← get).split.resolved.foldM (init := false) fun flag { expr := c' } => do
    if flag then
      return true
    else
      return c'.isApp && (← get).isCongruent c c'

private def checkDefaultSplitStatus (e : Expr) : GoalM SplitStatus := do
  match_expr e with
  | Or a b => checkDisjunctStatus e a b
  | And a b => checkConjunctStatus e a b
  | Eq _ a b =>
    if isMorallyIff e then
      checkIffStatus e a b
    else
      return .ready 2
  | _ =>
    if isIte e || isDIte e then
      return (← checkIteCondStatus (e.getArg! 1))
    if (← isResolvedCaseSplit e) then
      trace_goal[grind.debug.split] "split resolved: {e}"
      return .resolved
    if (← isCongrToPrevSplit e) then
      return .resolved
    if let some info := isMatcherAppCore? (← getEnv) e then
      return .ready info.numAlts
    if let .const declName .. := e.getAppFn then
      if let some info ← isInductivePredicate? declName then
        if (← isEqTrue e) then
          return .ready info.ctors.length info.isRec
    if e.isFVar then
      let type ← whnfD (← inferType e)
      let report : GoalM Unit := do
        reportIssue! "cannot perform case-split on {e}, unexpected type{indentExpr type}"
      let .const declName _ := type.getAppFn | report; return .resolved
      let .inductInfo info ← getConstInfo declName | report; return .resolved
      return .ready info.ctors.length info.isRec
    return .notReady

def checkSplitInfoArgStatus (a b : Expr) (eq : Expr) : GoalM SplitStatus := do
  if (← isEqTrue eq <||> isEqFalse eq) then return .resolved
  let is := (← get).split.argPosMap[(a, b)]? |>.getD []
  let mut j := a.getAppNumArgs
  let mut it_a := a
  let mut it_b := b
  repeat
    unless it_a.isApp && it_b.isApp do return .ready 2
    j := j - 1
    if j ∉ is then
      let arg_a := it_a.appArg!
      let arg_b := it_b.appArg!
      unless (← isEqv arg_a arg_b) do
        trace_goal[grind.split] "may be irrelevant\na: {a}\nb: {b}\neq: {eq}\narg_a: {arg_a}\narg_b: {arg_b}, gen: {← getGeneration eq}"
        /-
        We tried to return `.notReady` because we would not be able to derive a congruence, but
        `grind_ite.lean` breaks when this heuristic is used. TODO: understand better why.
        -/
        return .ready 2 (tryPostpone := true)
    it_a := it_a.appFn!
    it_b := it_b.appFn!
  return .ready 2

private def checkForallStatus (imp : Expr) (h : imp.isForall) : GoalM SplitStatus := do
  if (← isEqTrue imp) then
    let p := imp.forallDomain h
    let q := imp.forallBody h
    if (← isEqTrue p <||> isEqFalse p) then
      return .resolved
    unless q.hasLooseBVars do
      if (← isEqTrue q <||> isEqFalse q) then
        return .resolved
    return .ready 2
  else if (← isEqFalse imp) then
    return .resolved
  else
    return .notReady

def checkSplitStatus (s : SplitInfo) : GoalM SplitStatus := do
  match s with
  | .default e _    => checkDefaultSplitStatus e
  | .imp e h _      => checkForallStatus e h
  | .arg a b _ eq _ => checkSplitInfoArgStatus a b eq

private inductive SplitCandidate where
  | none
  | some (c : SplitInfo) (numCases : Nat) (isRec : Bool) (tryPostpone : Bool)

/--
Returns `true`, if there are no anchor references restricting the search,
or there is an anchor references `ref` s.t. `ref` matches `c`.
-/
private def checkAnchorRefs (c : SplitInfo) : GrindM Bool := do
  let some anchorRefs ← getAnchorRefs | return true
  let anchor ← c.getAnchor
  return anchorRefs.any (·.matches anchor)

/-- Returns the next case-split to be performed. It uses a very simple heuristic. -/
private def selectNextSplit? : GoalM SplitCandidate := do
  if (← isInconsistent) then return .none
  if (← checkMaxCaseSplit) then return .none
  go (← get).split.candidates .none []
where
  go (cs : List SplitInfo) (c? : SplitCandidate) (cs' : List SplitInfo) : GoalM SplitCandidate := do
    match cs with
    | [] =>
      modify fun s => { s with split.candidates := cs'.reverse }
      if let .some .. := c? then
        -- Remark: we reset `numEmatch` after each case split.
        -- We should consider other strategies in the future.
        modify fun s => { s with ematch.num := 0 }
      return c?
    | c::cs =>
    if !(← checkAnchorRefs c) then
      /-
      **Note**: `grind`s context contains anchor references restricting the
      case-splits that can be performed, and `c` does not matches any of
      the references provided.
      -/
      go cs c? cs'
    else
      trace_goal[grind.debug.split] "checking: {c.getExpr}"
      match (← checkSplitStatus c) with
      | .notReady => go cs c? (c::cs')
      | .resolved => go cs c? cs'
      | .ready numCases isRec tryPostpone =>
      if (← cheapCasesOnly) && numCases > 1 then
        go cs c? (c::cs')
      else match c? with
      | .none => go cs (.some c numCases isRec tryPostpone) cs'
      | .some c' numCases' _ tryPostpone' =>
      let isBetter : GoalM Bool := do
        if tryPostpone' && !tryPostpone then
          return true
        else if tryPostpone && !tryPostpone' then
          return false
        else if numCases == 1 && !isRec && numCases' > 1 then
          return true
        /-
        **Note**: We used to use `getGeneration c.getExpr` instead of `c.getGeneration`.
        This was incorrect. The expression returned by `c.getExpr` may have not been internalized yet.
        -/
        else if (← c.getGeneration) < (← c'.getGeneration) then
          return true
        return numCases < numCases'
      if (← isBetter) then
          go cs (.some c numCases isRec tryPostpone) (c'::cs')
        else
          go cs c? (c::cs')

private def mkGrindEM (c : Expr) :=
  mkApp (mkConst ``Lean.Grind.em) c

/-- Constructs a major premise for the `cases` tactic used by `grind`. -/
private def mkCasesMajor (c : Expr) : GoalM Expr := do
  match_expr c with
  | And a b => return mkApp3 (mkConst ``Grind.or_of_and_eq_false) a b (← mkEqFalseProof c)
  | Eq _ a b =>
    if isMorallyIff c then
      if (← isEqTrue c) then
        return mkApp3 (mkConst ``Grind.of_eq_eq_true) a b (← mkEqTrueProof c)
      else
        return mkApp3 (mkConst ``Grind.of_eq_eq_false) a b (← mkEqFalseProof c)
    else
      -- model-based theory combination split
      return mkGrindEM c
  | Not e => return mkGrindEM e
  | _ =>
    if isIte c || isDIte c then
      return mkGrindEM (c.getArg! 1)
    else if (← isEqTrue c) then
      return mkOfEqTrueCore c (← mkEqTrueProof c)
    else
      return c

private def casesWithTrace (mvarId : MVarId) (major : Expr) : GoalM (List MVarId) := do
  if (← getConfig).trace then
    if let .const declName _ := (← whnfD (← inferType major)).getAppFn then
      saveCases declName
  cases mvarId major

structure SplitCandidateWithAnchor where
  c        : SplitInfo
  numCases : Nat
  isRec    : Bool
  e        : Expr
  anchor   : UInt64

instance : HasAnchor SplitCandidateWithAnchor where
  getAnchor e := e.anchor

structure SplitCandidateAnchors where
  /-- Pairs `(anchor, split)` -/
  candidates : Array SplitCandidateWithAnchor
  /-- Number of digits (≥ 4) sufficient for distinguishing anchors. We usually display only the first `numDigits`. -/
  numDigits  : Nat

/--
Returns case-split candidates. Case-splits that are tagged as `.resolved` or `.notReady` are skipped.
Applies additional `filter` if provided.
-/
def getSplitCandidateAnchors (filter : Expr → GoalM Bool := fun _ => return true) : GoalM SplitCandidateAnchors := do
  let candidates := (← get).split.candidates
  let candidates ← candidates.toArray.filterMapM fun c => do
    let e := c.getExpr
    let anchor ← c.getAnchor
    let status ← checkSplitStatus c
    -- **Note**: we ignore case-splits that are not ready or have already been resolved.
    -- We may consider adding an option for including "not-ready" splits in the future.
    match status with
    | .resolved | .notReady => return none
    | .ready numCases isRec _ =>
      if (← filter e) then
        return some { e, c, numCases, isRec, anchor }
      else
        return none
  -- **TODO**: Add an option for including propositions that are only considered when using `+splitImp`
  -- **TODO**: Add an option for including terms whose type is an inductive predicate or type
  let numDigits := getNumDigitsForAnchors candidates
  return { candidates, numDigits }

namespace Action

/--
Given a `mvarId` associated with a subgoal created by `splitCore`, inspects the
proof term assigned to `mvarId` and tries to extract the proof of `False` that does not
depend on hypotheses introduced in the subgoal.
For example: suppose the subgoal is of the form `p → q → False` where `p` and `q` are new
hypotheses introduced during case analysis. If the proof is of the form `fun _ _ => h`, returns
`some h`.
-/
private def getFalseProof? (mvarId : MVarId) : MetaM (Option Expr) := mvarId.withContext do
  let proof ← instantiateMVars (mkMVar mvarId)
  if proof.hasSyntheticSorry then
    /- **Note**: We do not perform non-chronological backtracking if the proof
    contains synthetic `sorry`. -/
    return none
  else
    go proof
where
  go (proof : Expr) : MetaM (Option Expr) := do
    match_expr proof with
    | False.elim _ p => return some p
    | False.casesOn _ p => return some p
    | id α p => if α.isFalse then return some p else return none
    | _ =>
      /-
      **Note**: `intros` tactics may hide the `False` proof behind a `casesOn`
      For example: suppose the subgoal has a type of the form `p₁ → q₁ ∧ q₂ → p₂ → False`
      The proof will be of the form `fun _ h => h.casesOn (fun _ _ => hf)` where `hf` is the proof
      of `False` we are looking for.
      Non-chronological backtracking currently fails in this kind of example.
      -/
      let .lam _ _ b _ := proof | return none
      if b.hasLooseBVars then return none
      go b

/-- Returns `true` if the given list can be compressed using `<;>` at `splitCore` -/
private def isCompressibleSeq (seq : List (TSyntax `grind)) : Bool :=
  seq.all fun tac => match tac with
    | `(grind| next $_* => $_:grindSeq) => false
    | `(grind| · $_:grindSeq) => false
    | _ => true

/--
Given `[t₁, ..., tₙ]`, returns `t₁ <;> ... <;> tₙ`
-/
private def mkAndThenSeq (seq : List (TSyntax `grind)) : CoreM (TSyntax `grind) := do
  match seq with
  | [] => `(grind| done)
  | [tac] => return tac
  | tac :: seq =>
    let seq ← mkAndThenSeq seq
    `(grind| $tac:grind <;> $seq:grind)

private def mkCasesAndThen (cases : TSyntax `grind) (seq : List (TSyntax `grind)) : CoreM (TSyntax `grind) := do
  match seq with
  | [] => return cases
  | seq =>
    let seq ← mkAndThenSeq seq
    `(grind| $cases:grind <;> $seq:grind)

private def isCompressibleAlts (alts : Array (List (TSyntax `grind))) : Bool :=
  if _ : alts.size > 0 then
    let alt := alts[0]
    isCompressibleSeq alt && alts.all (· == alt)
  else
    true

def isSorryAlt (alt : List (TSyntax `grind)) : Bool :=
  match alt with
  | [tac] => match tac with
    | `(grind| sorry) => true
    | _ => false
  | _ => false

private def mkCasesResultSeq (cases : TSyntax `grind) (alts : Array (List (TSyntax `grind)))
    (compress : Bool) : CoreM (List (TSyntax `grind)) := do
  if compress && isCompressibleAlts alts then
    if alts.size > 0 then
      let firstAlt := alts[0]!
      if isSorryAlt firstAlt then
        /-
        **Note**: It is a bit pointless to return a script of the form `cases #<anchor> <;> sorry`
        -/
        return firstAlt
      else
        return [(← mkCasesAndThen cases firstAlt)]
    else
      return [cases]
  else
    let seq ← if h : alts.size = 1 then
      pure alts[0]
    else
      alts.toList.mapM fun s => mkGrindNext s
    return cases :: seq

/--
Performs a case-split using `c`.
Remark: `numCases` and `isRec` are computed using `checkSplitStatus`.
-/
def splitCore (c : SplitInfo) (numCases : Nat) (isRec : Bool)
    (stopAtFirstFailure : Bool)
    (compress : Bool) : Action := fun goal _ kp => do
  let traceEnabled := (← getConfig).trace
  let mvarId ← goal.mkAuxMVar
  let cExpr := c.getExpr
  let ((mvarIds, numDigits), goal) ← GoalM.run goal do
    let gen ← getGeneration cExpr
    let genNew := if numCases > 1 || isRec then gen+1 else gen
    saveSplitDiagInfo cExpr genNew numCases c.source
    markCaseSplitAsResolved cExpr
    trace_goal[grind.split] "{cExpr}, generation: {gen}"
    let mvarIds ← if let .imp e h _ := c then
      casesWithTrace mvarId (mkGrindEM (e.forallDomain h))
    else if (← isMatcherApp cExpr) then
      casesMatch mvarId cExpr
    else
      casesWithTrace mvarId (← mkCasesMajor cExpr)
    let numDigits ← if traceEnabled then
      pure (← getSplitCandidateAnchors).numDigits
    else
      pure 0
    return (mvarIds, numDigits)
  let numSubgoals := mvarIds.length
  /-
  **Split counter heuristic**: We do not increment `numSplits` for the first case (`i = 0`)
  of a non-recursive split. This leverages non-chronological backtracking: if the first case
  is solved using a proof that doesn't depend on the case hypothesis, we backtrack and close
  the original goal directly. In this scenario, the case-split was "free", it didn't contribute
  to the proof. By not counting it, we allow deeper exploration when case-splits turn out to be
  irrelevant.

  For recursive types or subsequent cases (`i > 0`), we always increment the counter since
  these represent genuine branches in the proof search.
  -/
  let subgoals := mvarIds.mapIdx fun i mvarId =>
    let numSplits := goal.split.num
    let numSplits := if i > 0 || isRec then numSplits + 1 else numSplits
    { goal with
      mvarId
      split.num := numSplits
      split.trace := { expr := cExpr, i, num := numSubgoals, source := c.source } :: goal.split.trace }
  let mut seqNew : Array (List (TSyntax `grind)) := #[]
  let mut stuckNew : Array Goal := #[]
  for subgoal in subgoals do
    match (← kp subgoal) with
    | .stuck gs =>
      if stopAtFirstFailure then
        /-
        **Note**: We don't need to assign `goal.mvarId` when `stopAtFirstFailure = true`
        because the caller will not be able to process the all failure/stuck goals anyway.
        -/
        return .stuck gs
      else
        stuckNew := stuckNew ++ gs
    | .closed seq =>
      if let some falseProof ← getFalseProof? subgoal.mvarId then
        goal.mvarId.assignFalseProof falseProof
        return .closed seq
      else if !seq.isEmpty then
        /- **Note**: if the sequence is empty, it means the user will never see this goal. -/
        seqNew := seqNew.push seq
  if (← goal.mvarId.getType).isFalse then
    /- **Note**: We add the marker to assist `getFalseExpr?` -/
    goal.mvarId.assign (mkExpectedPropHint (← instantiateMVars (mkMVar mvarId)) (mkConst ``False))
  else
    goal.mvarId.assign (← instantiateMVars (mkMVar mvarId))
  if stuckNew.isEmpty then
    if traceEnabled then
      let anchor ← goal.withContext <| getAnchor cExpr
      let cases ← `(grind| cases $(← mkAnchorSyntax numDigits anchor):anchor)
      return .closed (← mkCasesResultSeq cases seqNew compress)
    else
      return .closed []
  else
    return .stuck stuckNew.toList

/--
Selects a case-split from the list of candidates, performs the split and applies
continuation to all subgoals.
If a subgoal is solved without using new hypotheses, closes the original goal using this proof. That is,
it performs non-chronological backtracking.

If `stopsAtFirstFailure = true`, it stops the search as soon as the given continuation cannot solve a subgoal.

If `compress = true`, then it uses `<;>` to generate the resulting tactic sequence if all subgoal sequences are
identical. For example, suppose that the following sequence is generated with `compress = false`
```
cases #50fc
next => lia
next => lia
```
Then with `compress = true` it generates `cases #50fc <;> lia`
-/
def splitNext (stopAtFirstFailure := true) (compress := true) : Action := fun goal kna kp => do
  let (r, goal) ← GoalM.run goal selectNextSplit?
  let .some c numCases isRec _ := r
    | kna goal
  let cExpr := c.getExpr
  let gen := goal.getGeneration cExpr
  let genNew := if numCases > 1 || isRec then gen+1 else gen
  let x : Action := splitCore c numCases isRec stopAtFirstFailure compress >> intros genNew >> assertAll
  x goal kna kp

end Action

end Lean.Meta.Grind
