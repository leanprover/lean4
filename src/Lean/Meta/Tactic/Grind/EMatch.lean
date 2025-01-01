/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Internalize

namespace Lean.Meta.Grind
/--
Theorem instance found using E-matching.
Recall that we only internalize new instances after we complete a full round of E-matching. -/
structure EMatchTheoremInstance where
  proof      : Expr
  prop       : Expr
  generation : Nat
  deriving Inhabited

namespace EMatch
/-! This module implements a simple E-matching procedure as a backtracking search. -/

/-- We represent an `E-matching` problem as a list of constraints. -/
inductive Cnstr where
  | /-- Matches pattern `pat` with term `e` -/
    «match» (pat : Expr) (e : Expr)
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
  deriving Inhabited

/-- State for the E-matching monad -/
structure State where
  /-- Choices that still have to be processed. -/
  choiceStack  : List Choice := []
  newInstances : Array EMatchTheoremInstance := #[]
  deriving Inhabited

abbrev M := ReaderT Context $ StateRefT State GoalM

def M.run' (x : M α) : GoalM α :=
  x {} |>.run' {}

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

/--
Matches arguments of pattern `p` with term `e`. Returns `some` if successful,
and `none` otherwise. It may update `c`s assignment and list of contraints to be
processed.
-/
private partial def matchArgs? (c : Choice) (p : Expr) (e : Expr) : OptionT GoalM Choice := do
  if !p.isApp then return c -- Done
  let pArg := p.appArg!
  let eArg := e.appArg!
  let goFn c := matchArgs? c p.appFn! e.appFn!
  if isPatternDontCare pArg then
    goFn c
  else if pArg.isBVar then
    goFn (← assign? c pArg.bvarIdx! eArg)
  else if let some pArg := groundPattern? pArg then
    guard (← isEqv pArg eArg)
    goFn c
  else
    goFn { c with cnstrs := .match pArg eArg :: c.cnstrs }

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
    if n.generation <= maxGeneration
       -- uses heterogeneous equality or is the root of its congruence class
       && (n.heqProofs || isSameExpr curr n.cgRoot)
       && eqvFunctions pFn curr.getAppFn
       && curr.getAppNumArgs == numArgs then
      if let some c ← matchArgs? c p curr |>.run then
        let gen := n.generation
        let c := { c with gen := Nat.max gen c.gen }
        modify fun s => { s with choiceStack := c :: s.choiceStack }
    curr ← getNext curr
    if isSameExpr curr e then break

/-- Processes `continue` contraint used to implement multi-patterns. -/
private def processContinue (c : Choice) (p : Expr) : M Unit := do
  let some apps := (← getThe Goal).appMap.find? p.toHeadIndex
    | return ()
  let maxGeneration ← getMaxGeneration
  for app in apps do
    let n ← getENode app
    if n.generation <= maxGeneration
       && (n.heqProofs || isSameExpr n.cgRoot app) then
      if let some c ← matchArgs? c p app |>.run then
        let gen := n.generation
        let c := { c with gen := Nat.max gen c.gen }
        modify fun s => { s with choiceStack := c :: s.choiceStack }

/--
Stores new theorem instance in the state.
Recall that new instances are internalized later, after a full round of ematching.
-/
private def addNewInstance (origin : Origin) (proof : Expr) (generation : Nat) : M Unit := do
  let proof ← instantiateMVars proof
  if grind.debug.proofs.get (← getOptions) then
    check proof
  let prop ← inferType proof
  trace[grind.ematch.instance] "{← origin.pp}: {prop}"
  modify fun s => { s with newInstances := s.newInstances.push { proof, prop, generation } }
  modifyThe Goal fun s => { s with numInstances := s.numInstances + 1 }

/--
After processing a (multi-)pattern, use the choice assignment to instantiate the proof.
Missing parameters are synthesized using type inference and type class synthesis."
-/
private partial def instantiateTheorem (c : Choice) : M Unit := withDefault do
  let thm := (← read).thm
  unless (← markTheorenInstance thm.proof c.assignment) do
    return ()
  trace[grind.ematch.instance.assignment] "{← thm.origin.pp}: {assignmentToMessageData c.assignment}"
  let proof ← thm.getProofWithFreshMVarLevels
  let numParams := thm.numParams
  assert! c.assignment.size == numParams
  let (mvars, bis, _) ← forallMetaBoundedTelescope (← inferType proof) numParams
  if mvars.size != thm.numParams then
    trace[grind.issues] "unexpected number of parameters at {← thm.origin.pp}"
    return ()
  -- Apply assignment
  for h : i in [:mvars.size] do
    let v := c.assignment[numParams - i - 1]!
    unless isSameExpr v unassigned do
      let mvarId := mvars[i].mvarId!
      unless (← mvarId.checkedAssign v) do
        trace[grind.issues] "type error constructing proof for {← thm.origin.pp}\nwhen assigning metavariable {mvars[i]} with {indentExpr v}"
        return ()
  -- Synthesize instances
  for mvar in mvars, bi in bis do
    if bi.isInstImplicit && !(← mvar.mvarId!.isAssigned) then
      let type ← inferType mvar
      unless (← synthesizeInstance mvar type) do
        trace[grind.issues] "failed to synthesize instance when instantiating {← thm.origin.pp}{indentExpr type}"
        return ()
  if (← mvars.allM (·.mvarId!.isAssigned)) then
    addNewInstance thm.origin (mkAppN proof mvars) c.gen
  else
    -- instance has hypothesis
    mkImp mvars 0 proof #[]
where
  synthesizeInstance (x type : Expr) : MetaM Bool := do
    let .some val ← trySynthInstance type | return false
    isDefEq x val

  mkImp (mvars : Array Expr) (i : Nat) (proof : Expr) (xs : Array Expr) : M Unit := do
    if h : i < mvars.size then
      let mvar := mvars[i]
      if (← mvar.mvarId!.isAssigned) then
        mkImp mvars (i+1) (mkApp proof mvar) xs
      else
        let mvarType ← instantiateMVars (← inferType mvar)
        if mvarType.hasExprMVar then
          let thm := (← read).thm
          trace[grind.issues] "failed to create hypothesis for instance of {← thm.origin.pp} hypothesis type has metavar with typer{indentExpr mvarType}"
          return ()
        withLocalDeclD (← mkFreshUserName `h) mvarType fun x => do
          mvar.mvarId!.assign x
          mkImp mvars (i+1) (mkApp proof x) (xs.push x)
    else
      let proof ← instantiateMVars proof
      let proof ← mkLambdaFVars xs proof
      let thm := (← read).thm
      addNewInstance thm.origin proof c.gen

/-- Process choice stack until we don't have more choices to be processed. -/
private partial def processChoices : M Unit := do
  unless (← get).choiceStack.isEmpty do
    checkSystem "ematch"
    if (← checkMaxInstancesExceeded) then return ()
    let c ← modifyGet fun s : State => (s.choiceStack.head!, { s with choiceStack := s.choiceStack.tail! })
    match c.cnstrs with
    | [] => instantiateTheorem c
    | .match p e :: cnstrs => processMatch { c with cnstrs } p e
    | .continue p :: cnstrs => processContinue { c with cnstrs } p
    processChoices

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
    if (n.heqProofs || isSameExpr n.cgRoot app) &&
       (!useMT || n.mt == gmt) then
      if let some c ← matchArgs? { cnstrs, assignment, gen := n.generation } p app |>.run then
        modify fun s => { s with choiceStack := [c] }
        processChoices

def ematchTheorem (thm : EMatchTheorem) : M Unit := do
  if (← checkMaxInstancesExceeded) then return ()
  withReader (fun ctx => { ctx with thm }) do
    let ps := thm.patterns
    match ps, (← read).useMT with
    | [p],   _     => main p []
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
def ematch : GoalM (Array EMatchTheoremInstance) := do
  let go (thms newThms : PArray EMatchTheorem) : EMatch.M (Array EMatchTheoremInstance) := do
    withReader (fun ctx => { ctx with useMT := true }) <| ematchTheorems thms
    withReader (fun ctx => { ctx with useMT := false }) <| ematchTheorems newThms
    return (← get).newInstances
  if (← checkMaxInstancesExceeded) then
    return #[]
  else
    let insts ← go (← get).thms (← get).newThms |>.run'
    modify fun s => { s with
      thms         := s.thms ++ s.newThms
      newThms      := {}
      gmt          := s.gmt + 1
    }
    return insts

end Lean.Meta.Grind
