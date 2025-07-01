/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.SearchM
import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr

namespace Lean.Meta.Grind.Arith.Linear

def IneqCnstr.throwUnexpected (c : IneqCnstr) : LinearM α := do
  throwError "`grind linarith` internal error, unexpected{indentD (← c.denoteExpr)}"

def DiseqCnstr.throwUnexpected (c : DiseqCnstr) : LinearM α := do
  throwError "`grind linarith` internal error, unexpected{indentD (← c.denoteExpr)}"

private def checkIsNextVar (x : Var) : LinearM Unit := do
  if x != (← getStruct).assignment.size then
    throwError "`grind linarith` internal error, assigning variable out of order"

private def traceAssignment (x : Var) (v : Rat) : LinearM Unit := do
  trace[grind.debug.linarith.search.assign] "{quoteIfArithTerm (← getVar x)} := {v}"

private def setAssignment (x : Var) (v : Rat) : LinearM Unit := do
  checkIsNextVar x
  traceAssignment x v
  modifyStruct fun s => { s with assignment := s.assignment.push v }

/--
Assuming all variables smaller than `x` have already been assigned,
returns the best lower bound for `x` using the given partial assignment and
inequality constraints where `x` is the maximal variable.
-/
def getBestLower? (x : Var) : LinearM (Option (Rat × IneqCnstr)) := do
  let s ← getStruct
  let mut best? := none
  for c' in s.lowers[x]! do
    let .add k _ p := c'.p | c'.throwUnexpected
    let some v ← p.eval? | c'.throwUnexpected
    let lower' := v / (-k)
    if let some (lower, c) := best? then
      if lower' > lower || (lower' == lower && c'.strict && !c.strict) then
        best? := some (lower', c')
    else
      best? := some (lower', c')
  return best?

/--
Assuming all variables smaller than `x` have already been assigned,
returns the best upper bound for `x` using the given partial assignment and
inequality constraints where `x` is the maximal variable.
-/
def getBestUpper? (x : Var) : LinearM (Option (Rat × IneqCnstr)) := do
  let s ← getStruct
  let mut best? := none
  for c' in s.uppers[x]! do
    let .add k _ p := c'.p | c'.throwUnexpected
    let some v ← p.eval? | c'.throwUnexpected
    let upper' := (-v) / k
    if let some (upper, c) := best? then
      if upper' < upper || (upper' == upper && c'.strict && !c.strict) then
        best? := some (upper', c')
    else
      best? := some (upper', c')
  return best?

/-- Returns values we cannot assign `x` because of disequality constraints. -/
def getDiseqValues (x : Var) : LinearM (Array (Rat × DiseqCnstr)) := do
  let s ← getStruct
  let mut r := #[]
  for c in s.diseqs[x]! do
    let .add k _ p := c.p | c.throwUnexpected
    let some v ← p.eval? | c.throwUnexpected
    r := r.push (((-v)/k), c)
  return r

def findDiseq? (v : Rat) (dvals : Array (Rat × DiseqCnstr)) : Option DiseqCnstr :=
  (·.2) <$> dvals.find? fun (v', _) => v' == v

def inDiseqValues (v : Rat) (dvals : Array (Rat × DiseqCnstr)) : Bool :=
  Option.isSome <| findDiseq? v dvals

partial def geAvoiding (v : Rat) (dvals : Array (Rat × DiseqCnstr)) : Rat :=
  if inDiseqValues v dvals then geAvoiding (v+1) dvals else v

partial def leAvoiding (v : Rat) (dvals : Array (Rat × DiseqCnstr)) : Rat :=
  if inDiseqValues v dvals then leAvoiding (v-1) dvals else v

def resolveLowerUpperConflict (c₁ c₂ : IneqCnstr) : LinearM Unit := do
  trace[grind.debug.linarith.search.conflict] "{← c₁.denoteExpr}, {← c₂.denoteExpr}"
  let .add a₁ _ p₁ := c₁.p | c₁.throwUnexpected
  let .add a₂ _ p₂ := c₂.p | c₂.throwUnexpected
  let p := p₁.mul a₂.natAbs |>.combine (p₂.mul a₁.natAbs)
  let c : IneqCnstr := { p, strict := c₁.strict || c₂.strict, h := .combine c₁ c₂ }
  c.assert

/--
Try to find integer between lower and upper bounds that is different for known disequalities
-/
partial def findInt? (lower : Rat) (lowerStrict : Bool) (upper : Rat) (upperStrict : Bool) (dvals : Array (Rat × DiseqCnstr)) : Option Rat :=
  let start := lower.ceil
  let start := if start == lower && lowerStrict then start + 1 else start
  let stop := upper.floor
  let stop := if stop == upper && upperStrict then stop - 1 else stop
  go start stop
where
  go (v : Int) (stop : Int) : Option Rat :=
    if v > stop then
      none
    else if inDiseqValues v dvals then
      go (v+1) stop
    else
      some v

/--
Find rational value in the interval `(lower, upper)` that is different from all known
disequalities.
-/
partial def findRat (lower : Rat) (upper : Rat) (dvals : Array (Rat × DiseqCnstr)) : Rat :=
  let mid := (lower + upper) / 2
  if inDiseqValues mid dvals then
    findRat mid upper dvals
  else
    mid

def DiseqCnstr.split (c : DiseqCnstr) : SearchM IneqCnstr := do
  let fvarId ← if let some fvarId := (← getStruct).diseqSplits.find? c.p then
    trace[grind.debug.linarith.search.split] "{← c.denoteExpr}, reusing {fvarId.name}"
    pure fvarId
  else
    let fvarId ← mkCase c
    trace[grind.debug.linarith.search.split] "{← c.denoteExpr}, {fvarId.name}"
    modifyStruct fun s => { s with diseqSplits := s.diseqSplits.insert c.p fvarId }
    pure fvarId
  return { p := c.p, strict := true, h := .dec fvarId }

/--
Given an inequality `c₁` which is a lower bound, i.e., leading coefficient is negative,
and a disequality `c`, splits `c` and resolve with `c₁`.
-/
def resolveLowerDiseqConflict (c₁ : IneqCnstr) (c : DiseqCnstr) : SearchM Unit := do
  let c := if c.p.leadCoeff < 0 then
    /-
    Ensure leading coefficient of the disequality is positive.
    Thus, after the split, we have an upper bound that can be resolved with `c₁`
    -/
    { p := c.p.mul (-1), h := .neg c : DiseqCnstr }
  else
    c
  let c₂ ← c.split
  resolveLowerUpperConflict c₁ c₂

def processVar (x : Var) : SearchM Unit := do
  let lower? ← getBestLower? x
  let upper? ← getBestUpper? x
  let diseqVals ← getDiseqValues x
  -- TODO: sanity check for variable `One.one`.
  -- Recall that `One.one` must be the smallest variable.
  match lower?, upper? with
  | none, none =>
    let v := geAvoiding 0 diseqVals
    trace[grind.debug.linarith.search] "v: {v}, diseqs: {diseqVals.map (·.1)}"
    setAssignment x v
  | some (lower, _), none =>
    let v := geAvoiding (lower.ceil + 1) diseqVals
    trace[grind.debug.linarith.search] "v: {v}, lower: {lower}, diseqs: {diseqVals.map (·.1)}"
    setAssignment x v
  | none, some (upper, _) =>
    let v := geAvoiding (upper.floor - 1) diseqVals
    trace[grind.debug.linarith.search] "v: {v}, upper: {upper}, diseqs: {diseqVals.map (·.1)}"
    setAssignment x v
  | some (lower, c₁), some (upper, c₂) =>
    if lower > upper || (lower == upper && (c₁.strict || c₂.strict)) then
      resolveLowerUpperConflict c₁ c₂
    else if lower == upper then
      if let some d := findDiseq? lower diseqVals then
        /-
        Remark: We are currently eagerly splitting `a = b` into `a ≤ b` and `b ≤ a`.
        Thus, even if `c₁.p == -c₂.p`, we can only combine them back into an equality
        if the order is partial.
        -- TODO: eliminate variables using equations eagerly like we do in the cutsat module.
        -/
        if (← isLinearOrder) then
          resolveLowerDiseqConflict c₁ d
        else
          -- TODO: if we have a partial order and `c₁.p == -c₂.p`,
          -- we can generate an equality and resolve it with the disequality.
          let diseq ← d.denoteExpr
          -- Remark: we filter duplicates before displaying diagnostics to users
          modifyStruct fun s => { s with ignored := s.ignored.push diseq }
          trace[grind.debug.linarith.search] "v: {lower}, lower, upper: {lower}, **ignore diseq**, diseqs: {diseqVals.map (·.1)}"
          setAssignment x lower
      else
        trace[grind.debug.linarith.search] "v: {lower}, lower, upper: {lower}, diseqs: {diseqVals.map (·.1)}"
        setAssignment x lower
    else
      let v := if let some v := findInt? lower c₁.strict upper c₂.strict diseqVals then
        v
      else
        findRat lower upper diseqVals
      trace[grind.debug.linarith.search] "v: {v}, lower: {lower}, upper: {upper}, diseqs: {diseqVals.map (·.1)}"
      setAssignment x v

/-- Returns `true` if we already have a complete assignment / model. -/
def hasAssignment : LinearM Bool := do
  return (← getStruct).vars.size == (← getStruct).assignment.size

private def findCase (decVars : FVarIdSet) : SearchM Case := do
  repeat
    let numCases := (← get).cases.size
    assert! numCases > 0
    let case := (← get).cases[numCases-1]!
    modify fun s => { s with cases := s.cases.pop }
    if decVars.contains case.fvarId then
      return case
    -- Conflict does not depend on this case.
    trace[grind.debug.linarith.search.backtrack] "skipping {case.fvarId.name}"
  unreachable!

def resolveConflict (h : UnsatProof) : SearchM Unit := do
  trace[grind.debug.linarith.search.backtrack] "resolve conflict, decision stack: {(← get).cases.toList.map fun c => c.fvarId.name}"
  let decVars := h.collectDecVars.run (← get).decVars
  trace[grind.debug.linarith.search.backtrack] "dec vars: {decVars.toList.map (·.name)}"
  if decVars.isEmpty then
    closeGoal (← h.toExprProof)
    return ()
  let c ← findCase decVars
  modifyStruct fun _  => c.saved
  trace[grind.debug.linarith.search.backtrack] "backtracking {c.fvarId.name}"
  let decVars := decVars.erase c.fvarId
  let decVars := decVars.toArray
  let p' := c.c.p.mul (-1)
  let c' := { p := p', strict := true, h := .ofDiseqSplit c.c c.fvarId h decVars : IneqCnstr }
  trace[grind.debug.linarith.search.backtrack] "resolved diseq split: {← c'.denoteExpr}"
  c'.assert

/-- Search for an assignment/model for the linear constraints. -/
private def searchAssignmentMain : SearchM Unit := do
  repeat
    trace[grind.debug.linarith.search] "main loop"
    checkSystem "linarith"
    if (← hasAssignment) then
      return ()
    if (← isInconsistent) then
      -- `grind` state is inconsistent
      return ()
    if let some c := (← getStruct).conflict? then
      resolveConflict c
    else
      let x : Var := (← getStruct).assignment.size
      trace[grind.debug.linarith.search] "next var: {← getVar x}, {x}, {(← getStruct).assignment.toList}"
      processVar x

private def searchAssignment : LinearM Unit := do
  searchAssignmentMain |>.run' {}

/--
Returns `true` if work/progress has been done.
There are two kinds of progress:
- An assignment for satisfying constraints was constructed.
- An inconsistency was detected.

The result is `false` if module for every structure already has an assignment.
-/
def check : GoalM Bool := do
  let mut progress := false
  for structId in [:(← get').structs.size] do
    let r ← LinearM.run structId do
      if (← hasAssignment) then
        return false
      searchAssignment
      return true
    progress := progress || r
    if (← isInconsistent) then
      return true
  return progress

end Lean.Meta.Grind.Arith.Linear
