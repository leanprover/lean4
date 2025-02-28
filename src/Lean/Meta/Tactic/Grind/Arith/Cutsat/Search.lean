/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM

namespace Lean.Meta.Grind.Arith.Cutsat

private def checkIsNextVar (x : Var) : GoalM Unit := do
  if x != (← get').assignment.size then
    throwError "`grind` internal error, assigning variable out of order"

private def setAssignment (x : Var) (v : Rat) : GoalM Unit := do
  checkIsNextVar x
  trace[grind.cutsat.assign] "{quoteIfNotAtom (← getVar x)} := {v}"
  modify' fun s => { s with assignment := s.assignment.push v }

private def skipAssignment (x : Var)  : GoalM Unit := do
  checkIsNextVar x
  modify' fun s => { s with assignment := s.assignment.push 0 }

/-- Assign eliminated variables using `elimEqs` field. -/
private def assignElimVars : GoalM Unit := do
  go (← get').elimStack
where
  go (xs : List Var) : GoalM Unit := do
    match xs with
    | [] => return ()
    | x :: xs =>
      let some c := (← get').elimEqs[x]!
        | throwError "`grind` internal error, eliminated variable must have equation associated with it"
      let .add a _ p := c.p | c.throwUnexpected
      let some v ← p.eval? | c.throwUnexpected
      let v := (-v) / a
      modify' fun s => { s with assignment := s.assignment.set x v }
      go xs

/--
Assuming all variables smaller than `x` have already been assigned,
returns the best lower bound for `x` using the given partial assignment and
inequality constraints where `x` is the maximal variable.
-/
def getBestLower? (x : Var) : GoalM (Option (Rat × LeCnstr)) := do
  let s ← get'
  let mut best? := none
  for c in s.lowers[x]! do
    let .add k _ p := c.p | c.throwUnexpected
    let some v ← p.eval? | c.throwUnexpected
    let lower' := v / (-k)
    if let some (lower, _) := best? then
      if lower' > lower then
        best? := some (lower', c)
    else
      best? := some (lower', c)
  return best?

/--
Assuming all variables smaller than `x` have already been assigned,
returns the best upper bound for `x` using the given partial assignment and
inequality constraints where `x` is the maximal variable.
-/
def getBestUpper? (x : Var) : GoalM (Option (Rat × LeCnstr)) := do
  let s ← get'
  let mut best? := none
  for c in s.uppers[x]! do
    let .add k _ p := c.p | c.throwUnexpected
    let some v ← p.eval? | c.throwUnexpected
    let upper' := (-v) / k
    if let some (upper, _) := best? then
      if upper' < upper then
        best? := some (upper', c)
    else
      best? := some (upper', c)
  return best?

/-- Returns values we cannot assign `x` because of disequality constraints. -/
def getDiseqValues (x : Var) : SearchM (Array (Rat × DiseqCnstr)) := do
  let s ← get'
  let mut r := #[]
  for c in s.diseqs[x]! do
    let .add k _ p := c.p | c.throwUnexpected
    let some v ← p.eval? | c.throwUnexpected
    if (← isApprox) then
      r := r.push (((-v)/k), c)
    else
      -- We are building an integer model,
      -- if `k` does not divide `v`, we can just ignore the disequality.
      let v := v.num
      if v % k == 0 then
        r := r.push (v / k, c)
  return r

/--
Solution space for a divisibility constraint of the form `d ∣ a*x + b`
See `DvdCnstr.getSolutions?` to understand how it is computed.
-/
structure DvdSolution where
  d : Int := 1
  b : Int := 0

def DvdCnstr.getSolutions? (c : DvdCnstr) : SearchM (Option DvdSolution) := do
  let d := c.d
  let .add a _ p := c.p | c.throwUnexpected
  let some b ← p.eval? | c.throwUnexpected
  if b.den != 1 then
    -- `b` is a rational number, mark model as imprecise, and ignore the constraint
    setImprecise
    return none
  let b := b.num
  -- We must solve `d ∣ a*x + b`
  let g := d.gcd a
  if b % g != 0 then
    return none -- no solutions
  let d := d / g
  let a := a / g
  let b := b / g
  -- `α*a + β*d = 1`
  -- `α*a = 1 (mod d)`
  let (_, α, _β) := gcdExt a d
  -- `a'*a = 1 (mod d)`
  let a' := if α < 0 then α % d else α
  -- `a*x = -b (mod d)`
  -- `x = -b*a' (mod d)`
  -- `x = k*d + -b*a'` for any k
  return some { d, b := -b*a' }

def resolveDvdConflict (c : DvdCnstr) : GoalM Unit := do
  trace[grind.cutsat.conflict] "{← c.pp}"
  let d := c.d
  let .add a _ p := c.p | c.throwUnexpected
  (← mkDvdCnstr (a.gcd d) p (.elim c)).assert

/--
Given a divisibility constraint solution space `s := { b, d }`,
and a candidate assignment `v`, we want to find
an assignment `w` such that `w ≥ v` such that exists `k`, `w = k*d + b`
Thus,
- `k*d + b ≥ v`
- `k ≥ cdiv (v - b) d`
So, we take `w = (cdiv (v - b) d)*d + b`
-/
def DvdSolution.ge (s : DvdSolution) (v : Int) : Int :=
  (Int.Linear.cdiv (v - s.b) s.d)*s.d + s.b

/--
Given a divisibility constraint solution space `s := { b, d }`,
and a candidate assignment `v`, we want to find
an assignment `w` such that `w ≤ v` such that exists `k`, `w = k*d + b`
Thus,
- `k*d + b ≤ v`
- `k ≤ (v - b) / d`
So, we take `w = ((v - b) / d)*d + b`
-/
def DvdSolution.le (s : DvdSolution) (v : Int) : Int :=
  ((v - s.b)/s.d)*s.d + s.b

def findDiseq? (v : Int) (dvals : Array (Rat × DiseqCnstr)) : Option DiseqCnstr :=
  (·.2) <$> dvals.find? fun (d, _) =>
    d.den == 1 && d.num == v

def inDiseqValues (v : Int) (dvals : Array (Rat × DiseqCnstr)) : Bool :=
  Option.isSome <| findDiseq? v dvals

def findRatDiseq? (v : Rat) (dvals : Array (Rat × DiseqCnstr)) : Option DiseqCnstr :=
  (·.2) <$> dvals.find? fun (d, _) => v == d

partial def DvdSolution.geAvoiding (s : DvdSolution) (v : Int) (dvals : Array (Rat × DiseqCnstr)) : Int :=
  let v := s.ge v
  if inDiseqValues v dvals then
    geAvoiding s (v+1) dvals
  else
    v

partial def DvdSolution.leAvoiding (s : DvdSolution) (v : Int) (dvals : Array (Rat × DiseqCnstr)) : Int :=
  let v := s.le v
  if inDiseqValues v dvals then
    geAvoiding s (v-1) dvals
  else
    v

inductive FindIntValResult where
  | found (val : Int)
  | diseq (c : DiseqCnstr)
  | dvd
  deriving Inhabited

/--
Tries to find an integer `v` s.t. `lower ≤ v ≤ upper`, `v ∉ dvals`, and `v ∈ s`.
Returns `.found v` if result was found, `.dvd` if it failed because of the divisibility constraint,
and `.diseq c` because of the disequality constraint `c`.
-/
partial def findIntVal (s : DvdSolution) (lower : Int) (upper : Int) (dvals : Array (Rat × DiseqCnstr)) : FindIntValResult :=
  let v := s.ge lower
  if v > upper then
    .dvd
  else
    go v
where
  go (v : Int) : FindIntValResult :=
    if let some c := findDiseq? v dvals then
      let v := s.ge (v+1)
      if v > upper then .diseq c else go v
    else
      .found v

partial def findRatVal (lower upper : Rat) (diseqVals : Array (Rat × DiseqCnstr)) : Rat :=
  let v := (lower + upper)/2
  if (findRatDiseq? v diseqVals).isSome then
    findRatVal lower v diseqVals
  else
    v

def resolveRealLowerUpperConflict (c₁ c₂ : LeCnstr) : GoalM Bool := do
  trace[grind.cutsat.conflict] "{← c₁.pp}, {← c₂.pp}"
  let .add a₁ _ p₁ := c₁.p | c₁.throwUnexpected
  let .add a₂ _ p₂ := c₂.p | c₂.throwUnexpected
  let p := p₁.mul a₂.natAbs |>.combine (p₂.mul a₁.natAbs)
  if (← p.satisfiedLe) != .false then
    return false
  else
    let c ← mkLeCnstr p (.combine c₁ c₂)
    c.assert
    return true

def resolveCooperLeft (c₁ c₂ : LeCnstr) : GoalM Unit := do
  throwError "Cooper-left NIY {← c₁.pp} {← c₂.pp}"

def resolveCooperRight (c₁ c₂ : LeCnstr) : GoalM Unit := do
  throwError "Cooper-right NIY {← c₁.pp} {← c₂.pp}"

def resolveCooper (c₁ c₂ : LeCnstr) : GoalM Unit := do
  if c₁.p.leadCoeff.natAbs < c₂.p.leadCoeff.natAbs then
    resolveCooperLeft c₁ c₂
  else
    resolveCooperRight c₁ c₂

def resolveCooperDvdLeft (c₁ c₂ : LeCnstr) (c : DvdCnstr) : GoalM Unit := do
  throwError "Cooper-dvd-left NIY {← c₁.pp} {← c₂.pp} {← c.pp}"

def resolveCooperDvdRight (c₁ c₂ : LeCnstr) (c : DvdCnstr) : GoalM Unit := do
  throwError "Cooper-dvd-right NIY {← c₁.pp} {← c₂.pp} {← c.pp}"

def resolveCooperDvd (c₁ c₂ : LeCnstr) (c : DvdCnstr) : GoalM Unit := do
  if c₁.p.leadCoeff.natAbs < c₂.p.leadCoeff.natAbs then
    resolveCooperDvdLeft c₁ c₂ c
  else
    resolveCooperDvdRight c₁ c₂ c

def resolveCooperDiseq (c₁ : DiseqCnstr) (c₂ : LeCnstr) (_c? : Option DvdCnstr) : GoalM Unit := do
  throwError "Cooper-diseq NIY {← c₁.pp} {← c₂.pp}"

def resolveRatDiseq (c₁ : LeCnstr) (c : DiseqCnstr) : GoalM Unit := do
  throwError "diseq NIY {← c₁.pp} {← c.pp}"

def processVar (x : Var) : SearchM Unit := do
  if (← eliminated x) then
    /-
    Variable has been eliminated, and will be assigned later after we have assigned
    variables that have not been eliminated.
    -/
    skipAssignment x
    return ()
  -- Solution space for divisibility constraint is `x = k*d + b`
  let dvdSol ← if let some c := (← get').dvds[x]! then
    if let some solutions ← c.getSolutions? then
      pure solutions
    else
      resolveDvdConflict c
      return ()
  else
    pure {}
  let lower? ← getBestLower? x
  let upper? ← getBestUpper? x
  let diseqVals ← getDiseqValues x
  match lower?, upper? with
  | none, none =>
    let v := dvdSol.geAvoiding 0 diseqVals
    setAssignment x v
  | some (lower, _), none =>
    let lower := lower.ceil
    let v := dvdSol.geAvoiding lower diseqVals
    setAssignment x v
  | none, some (upper, _) =>
    let upper := upper.floor
    let v := dvdSol.leAvoiding upper diseqVals
    setAssignment x v
  | some (lower, c₁), some (upper, c₂) =>
    if lower > upper then
      let .true ← resolveRealLowerUpperConflict c₁ c₂
        | throwError "`grind` internal error, conflict resolution failed"
      return ()
    -- `lower ≤ upper` here
    if lower.ceil > upper.floor then
      if (← resolveRealLowerUpperConflict c₁ c₂) then
        -- Resolved conflict using "real" shadow
        return ()
      if !(← isApprox) then
        resolveCooper c₁ c₂
        return ()
    let r := findIntVal dvdSol lower.ceil upper.floor diseqVals
    if let .found v := r then
      setAssignment x v
      return ()
    if (← isApprox) then
      if lower < upper then
        setAssignment x <| findRatVal lower upper diseqVals
      else if let some c := findRatDiseq? lower diseqVals then
        resolveRatDiseq c₁ c
      else
        setAssignment x lower
    else
      match r with
      | .dvd => resolveCooperDvd c₁ c₂ (← get').dvds[x]!.get!
      | .diseq c => resolveCooperDiseq c c₂ (← get').dvds[x]!
      | _ => unreachable!

/-- Returns `true` if we already have a complete assignment / model. -/
def hasAssignment : GoalM Bool := do
  return (← get').vars.size == (← get').assignment.size

private def isDone : GoalM Bool := do
  if (← hasAssignment) then
    return true
  if (← inconsistent) then
    return true
  return false

/-- Search for an assignment/model for the linear constraints. -/
def searchAssigmentMain : SearchM Unit := do
  repeat
    if (← isDone) then
      return ()
    let x : Var := (← get').assignment.size
    -- TODO: resolve unsat conflicts
    processVar x

def searchAssigment : GoalM Unit := do
  -- TODO: .int case
  -- TODO:
  searchAssigmentMain .rat |>.run' {}

end Lean.Meta.Grind.Arith.Cutsat
