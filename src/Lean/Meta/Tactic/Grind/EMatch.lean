/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.DoNotSimp
import Lean.Meta.Tactic.Grind.MatchCond
import Lean.Meta.Tactic.Grind.Core

namespace Lean.Meta.Grind
namespace EMatch
/-! This module implements a simple E-matching procedure as a backtracking search. -/

/-- We represent an `E-matching` problem as a list of constraints. -/
inductive Cnstr where
  | /-- Matches pattern `pat` with term `e` -/
    «match» (pat : Expr) (e : Expr)
  | /-- Matches offset pattern `pat+k` with term `e` -/
    offset (pat : Expr) (k : Nat) (e : Expr)
  | /-- This constraint is used to encode multi-patterns. -/
    «continue» (pat : Expr)
  deriving Inhabited

/--
Internal "marker" for representing unassigned elemens in the `assignment` field.
This is a small hack to avoid one extra level of indirection by using `Option Expr` at `assignment`.
-/
private def unassigned : Expr := mkConst (Name.mkSimple "[grind_unassigned]")

private def assignmentToMessageData (assignment : Array Expr) : Array MessageData :=
  assignment.reverse.map fun e =>
    if isSameExpr e unassigned then m!"_" else m!"{e}"

/--
Choice point for the backtracking search.
The state of the procedure contains a stack of choices.
-/
structure Choice where
  /-- Contraints to be processed. -/
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
structure State where
  /-- Choices that still have to be processed. -/
  choiceStack  : List Choice := []
  deriving Inhabited

abbrev M := ReaderT Context $ StateRefT State GoalM

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
Returns `true` if the function `pFn` of a pattern is equivalent to the function `eFn`.
Recall that we ignore universe levels in patterns.
-/
private def eqvFunctions (pFn eFn : Expr) : Bool :=
  (pFn.isFVar && pFn == eFn)
  || (pFn.isConst && eFn.isConstOf pFn.constName!)

/-- Matches a pattern argument. See `matchArgs?`. -/
private def matchArg? (c : Choice) (pArg : Expr) (eArg : Expr) : OptionT GoalM Choice := do
  if isPatternDontCare pArg then
    return c
  else if pArg.isBVar then
    assign? c pArg.bvarIdx! eArg
  else if let some pArg := groundPattern? pArg then
    guard (← isEqv pArg eArg)
    return c
  else if let some (pArg, k) := isOffsetPattern? pArg then
    assert! Option.isNone <| isOffsetPattern? pArg
    assert! !isPatternDontCare pArg
    return { c with cnstrs := .offset pArg k eArg :: c.cnstrs }
  else
    return { c with cnstrs := .match pArg eArg :: c.cnstrs }

private def Choice.updateGen (c : Choice) (gen : Nat) : Choice :=
  { c with gen := Nat.max gen c.gen }

private def pushChoice (c : Choice) : M Unit :=
  modify fun s => { s with choiceStack := c :: s.choiceStack }

/--
Matches arguments of pattern `p` with term `e`. Returns `some` if successful,
and `none` otherwise. It may update `c`s assignment and list of contraints to be
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

/--
Matches pattern `p` with term `e` with respect to choice `c`.
We traverse the equivalence class of `e` looking for applications compatible with `p`.
For each candidate application, we match the arguments and may update `c`s assignments and contraints.
We add the updated choices to the choice stack.
-/
private partial def processMatch (c : Choice) (p : Expr) (e : Expr) : M Unit := do
  let maxGeneration ← getMaxGeneration
  let pFn := p.getAppFn
  let numArgs := p.getAppNumArgs
  let mut curr := e
  repeat
    let n ← getENode curr
    -- Remark: we use `<` because the instance generation is the maximum term generation + 1
    if n.generation < maxGeneration
       -- uses heterogeneous equality or is the root of its congruence class
       && (n.heqProofs || n.isCongrRoot)
       && eqvFunctions pFn curr.getAppFn
       && curr.getAppNumArgs == numArgs then
      if let some c ← matchArgs? c p curr |>.run then
        pushChoice (c.updateGen n.generation)
    curr ← getNext curr
    if isSameExpr curr e then break

/--
Matches offset pattern `pArg+k` with term `e` with respect to choice `c`.
-/
private partial def processOffset (c : Choice) (pArg : Expr) (k : Nat) (e : Expr) : M Unit := do
  let maxGeneration ← getMaxGeneration
  let mut curr := e
  repeat
    let n ← getENode curr
    if n.generation < maxGeneration then
      if let some (eArg, k') ← isOffset? curr |>.run then
        if k' < k then
          let c := c.updateGen n.generation
          pushChoice { c with cnstrs := .offset pArg (k - k') eArg :: c.cnstrs }
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
        if k' >= k then
          let eArg' := mkNatLit (k' - k)
          let eArg' ← shareCommon (← canon eArg')
          internalize eArg' (n.generation+1)
          if let some c ← matchArg? c pArg eArg' |>.run then
            pushChoice (c.updateGen n.generation)
    curr ← getNext curr
    if isSameExpr curr e then break

/-- Processes `continue` contraint used to implement multi-patterns. -/
private def processContinue (c : Choice) (p : Expr) : M Unit := do
  let some apps := (← getThe Goal).appMap.find? p.toHeadIndex
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
      markAsMatchCond d
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
    return mkApp4 (mkConst ``Grind.EqMatch f.constLevels!) α (← markAsDoNotSimp lhs) rhs initApp

/--
Stores new theorem instance in the state.
Recall that new instances are internalized later, after a full round of ematching.
-/
private def addNewInstance (origin : Origin) (proof : Expr) (generation : Nat) : M Unit := do
  let proof ← instantiateMVars proof
  if grind.debug.proofs.get (← getOptions) then
    check proof
  let mut prop ← inferType proof
  if Match.isMatchEqnTheorem (← getEnv) origin.key then
    prop ← annotateMatchEqnType prop (← read).initApp
  else if (← isEqnThm origin.key) then
    prop ← annotateEqnTypeConds prop
  trace_goal[grind.ematch.instance] "{← origin.pp}: {prop}"
  addTheoremInstance proof prop (generation+1)

/--
After processing a (multi-)pattern, use the choice assignment to instantiate the proof.
Missing parameters are synthesized using type inference and type class synthesis."
-/
private partial def instantiateTheorem (c : Choice) : M Unit := withDefault do withNewMCtxDepth do
  let thm := (← read).thm
  unless (← markTheoremInstance thm.proof c.assignment) do
    return ()
  trace_goal[grind.ematch.instance.assignment] "{← thm.origin.pp}: {assignmentToMessageData c.assignment}"
  let proof ← thm.getProofWithFreshMVarLevels
  let numParams := thm.numParams
  assert! c.assignment.size == numParams
  let (mvars, bis, _) ← forallMetaBoundedTelescope (← inferType proof) numParams
  if mvars.size != thm.numParams then
    reportIssue m!"unexpected number of parameters at {← thm.origin.pp}"
    return ()
  -- Apply assignment
  for h : i in [:mvars.size] do
    let mut v := c.assignment[numParams - i - 1]!
    unless isSameExpr v unassigned do
      let mvarId := mvars[i].mvarId!
      let mvarIdType ← mvarId.getType
      let vType ← inferType v
      let report : M Unit := do
        reportIssue m!"type error constructing proof for {← thm.origin.pp}\nwhen assigning metavariable {mvars[i]} with {indentExpr v}\n{← mkHasTypeButIsExpectedMsg vType mvarIdType}"
      unless (← isDefEq mvarIdType vType) do
        let some heq ← proveEq? vType mvarIdType
          | report
            return ()
        v ← mkAppM ``cast #[heq, v]
      unless (← mvarId.checkedAssign v) do
        report
        return ()
  -- Synthesize instances
  for mvar in mvars, bi in bis do
    if bi.isInstImplicit && !(← mvar.mvarId!.isAssigned) then
      let type ← inferType mvar
      unless (← synthesizeInstanceAndAssign mvar type) do
        reportIssue m!"failed to synthesize instance when instantiating {← thm.origin.pp}{indentExpr type}"
        return ()
  let proof := mkAppN proof mvars
  if (← mvars.allM (·.mvarId!.isAssigned)) then
    addNewInstance thm.origin proof c.gen
  else
    let mvars ← mvars.filterM fun mvar => return !(← mvar.mvarId!.isAssigned)
    if let some mvarBad ← mvars.findM? fun mvar => return !(← isProof mvar) then
      reportIssue m!"failed to instantiate {← thm.origin.pp}, failed to instantiate non propositional argument with type{indentExpr (← inferType mvarBad)}"
    let proof ← mkLambdaFVars (binderInfoForMVars := .default) mvars (← instantiateMVars proof)
    addNewInstance thm.origin proof c.gen

/-- Process choice stack until we don't have more choices to be processed. -/
private def processChoices : M Unit := do
  let maxGeneration ← getMaxGeneration
  while !(← get).choiceStack.isEmpty do
    checkSystem "ematch"
    if (← checkMaxInstancesExceeded) then return ()
    let c ← modifyGet fun s : State => (s.choiceStack.head!, { s with choiceStack := s.choiceStack.tail! })
    if c.gen < maxGeneration then
      match c.cnstrs with
      | [] => instantiateTheorem c
      | .match p e :: cnstrs => processMatch { c with cnstrs } p e
      | .offset p k e :: cnstrs => processOffset { c with cnstrs } p k e
      | .continue p :: cnstrs => processContinue { c with cnstrs } p

private def main (p : Expr) (cnstrs : List Cnstr) : M Unit := do
  let some apps := (← getThe Goal).appMap.find? p.toHeadIndex
    | return ()
  let numParams  := (← read).thm.numParams
  let assignment := mkArray numParams unassigned
  let useMT      := (← read).useMT
  let gmt        := (← getThe Goal).gmt
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
  let assignment := mkArray numParams unassigned
  let useMT      := (← read).useMT
  let gmt        := (← getThe Goal).gmt
  let false      ← getFalseExpr
  let mut curr   := false
  repeat
    if (← checkMaxInstancesExceeded) then return ()
    let n ← getENode curr
    if (n.heqProofs || n.isCongrRoot) &&
       (!useMT || n.mt == gmt) then
      let_expr Eq α lhs rhs := n.self | pure ()
      if (← isDefEq α pα) then
         let c₀ : Choice := { cnstrs := [], assignment, gen := n.generation }
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
def ematch : GoalM Unit := do
  let go (thms newThms : PArray EMatchTheorem) : EMatch.M Unit := do
    withReader (fun ctx => { ctx with useMT := true }) <| ematchTheorems thms
    withReader (fun ctx => { ctx with useMT := false }) <| ematchTheorems newThms
  if (← checkMaxInstancesExceeded <||> checkMaxEmatchExceeded) then
    return ()
  else
    go (← get).thms (← get).newThms |>.run'
    modify fun s => { s with
      thms         := s.thms ++ s.newThms
      newThms      := {}
      gmt          := s.gmt + 1
      numEmatch    := s.numEmatch + 1
    }

/-- Performs one round of E-matching, and assert new instances. -/
def ematchAndAssert : GrindTactic := fun goal => do
  let numInstances := goal.numInstances
  let goal ← GoalM.run' goal ematch
  if goal.numInstances == numInstances then
    return none
  assertAll goal

end Lean.Meta.Grind
