/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Internalize

namespace Lean.Meta.Grind

/-- Returns maximum term generation that is considered during ematching -/
private def getMaxGeneration : GoalM Nat := do
  return 10000 -- TODO

private def checkMaxInstancesExceeded : GoalM Bool := do
  return false -- TODO

namespace EMatch

inductive Cnstr where
  | «continue» (pat : Expr)
  | «match» (pat : Expr) (e : Expr)
  deriving Inhabited

-- Internal "marker" for representing unassigned elemens in the `assignment` field.
-- This is a small hack to avoid one extra level of indirection by using `Option Expr` at `assignment`.
private def unassigned : Expr := mkConst (Name.mkSimple "[grind_unassigned]")

structure Choice where
  cnstrs     : List Cnstr
  gen        : Nat
  assignment : Array Expr
  deriving Inhabited

structure TheoremInstance where
  prop       : Expr
  proof      : Expr
  generation : Nat
  deriving Inhabited

structure Context where
  useMT : Bool := true
  thm   : EMatchTheorem := default
  deriving Inhabited

structure State where
  choiceStack  : List Choice := []
  newInstances : PArray TheoremInstance := {}
  deriving Inhabited

abbrev M := ReaderT Context $ StateRefT State GoalM

def M.run' (x : M α) : GoalM α :=
  x {} |>.run' {}

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
where
  /--
  Matches arguments of pattern `p` with term `e`. Returns `some` if successful,
  and `none` otherwise. It may update `c`s assignment and list of contraints to be
  processed.
  -/
  matchArgs? (c : Choice) (p : Expr) (e : Expr) : OptionT GoalM Choice := do
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

private def processContinue (_c : Choice) (_p : Expr) : M Unit := do
  throwError "`processContinue` NIY"

private def assignmentToMessageData (assignment : Array Expr) : Array MessageData :=
  assignment.reverse.map fun e =>
    if isSameExpr e unassigned then m!"_" else m!"{e}"

private partial def instantiateTheorem (c : Choice) : M Unit := do
  trace[grind.ematch.instance] "{(← read).thm.origin.key} : {assignmentToMessageData c.assignment}"
  -- TODO
  return ()

private partial def processChoices : M Unit := do
  unless (← get).choiceStack.isEmpty do
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
    let n ← getENode app
    if (n.heqProofs || isSameExpr n.cgRoot app) &&
       (!useMT || n.mt == gmt) then
      modify fun s => { s with choiceStack := [] }
      processMatch { cnstrs, assignment, gen := n.generation } p app
      processChoices

def ematchTheorem (thm : EMatchTheorem) : M Unit := do
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

def internalizeNewInstances : M Unit := do
  -- TODO
  return ()

end EMatch

open EMatch

def ematch : GoalM Unit := do
  let go (thms newThms : PArray EMatchTheorem) : EMatch.M Unit := do
    withReader (fun ctx => { ctx with useMT := true }) <| ematchTheorems thms
    withReader (fun ctx => { ctx with useMT := false }) <| ematchTheorems newThms
    internalizeNewInstances
  unless (← checkMaxInstancesExceeded) do
    go (← get).thms (← get).newThms |>.run'
    modify fun s => { s with thms := s.thms ++ s.newThms, newThms := {}, gmt := s.gmt + 1 }

end Lean.Meta.Grind
