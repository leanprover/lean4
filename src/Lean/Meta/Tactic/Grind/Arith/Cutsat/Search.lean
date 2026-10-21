/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM
import Lean.Meta.Tactic.Simp.Arith.Int.Simp
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.ReorderVars
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
public section
namespace Lean.Meta.Grind.Arith.Cutsat

/-- Asserts constraints implied by a `CooperSplit`. -/
def CooperSplit.assert (cs : CooperSplit) : GoalM Unit := do
  let { c₁, c₂, c₃?, left, .. } := cs.pred
  let k   := cs.k
  let p₁  := c₁.p
  let p₂  := c₂.p
  let p   := p₁.tail
  let q   := p₂.tail
  let a   := p₁.leadCoeff
  let b   := p₂.leadCoeff
  let p₁' := p.mul b |>.combine (q.mul (-a))
  let p₁' := p₁'.addConst <| if left then b*k else (-a)*k
  let c₁' := { p := p₁', h := .cooper cs : LeCnstr }
  c₁'.assert
  if (← inconsistent) then return ()
  let d := if left then a else b
  if d.natAbs != 1 then
    let p₂' := if left then p else q
    let p₂' := p₂'.addConst k
    let c₂' := { d, p := p₂', h := .cooper₁ cs : DvdCnstr }
    c₂'.assert
    if (← inconsistent) then return ()
  let some c₃ := c₃? | return ()
  let p₃  := c₃.p
  let d   := c₃.d
  let s   := p₃.tail
  let c   := p₃.leadCoeff
  let c₃' := if left then
    let p₃' := p.mul c |>.combine (s.mul (-a))
    let p₃' := p₃'.addConst (c*k)
    { d := a*d, p := p₃', h := .cooper₂ cs : DvdCnstr }
  else
    let p₃' := q.mul (-c) |>.combine (s.mul b)
    let p₃' := p₃'.addConst (-c*k)
    { d := b*d, p := p₃', h := .cooper₂ cs : DvdCnstr }
  c₃'.assert

private def checkIsNextVar (x : Var) : GoalM Unit := do
  if x != (← get').assignment.size then
    throwError "`grind` internal error, assigning variable out of order"

private def traceAssignment (x : Var) (v : Rat) : GoalM Unit := do
  trace[grind.debug.lia.search.assign] "{quoteIfArithTerm (← getVar x)} := {v}"

private def setAssignment (x : Var) (v : Rat) : GoalM Unit := do
  checkIsNextVar x
  traceAssignment x v
  modify' fun s => { s with assignment := s.assignment.push v }

private def skipAssignment (x : Var)  : GoalM Unit := do
  checkIsNextVar x
  modify' fun s => { s with assignment := s.assignment.push 0 }

/-- Assign eliminated variables using `elimEqs` field. -/
private def assignElimVars : GoalM Unit := do
  if (← inconsistent) then return ()
  go (← get').elimStack
where
  go (xs : List Var) : GoalM Unit := do
    match xs with
    | [] => return ()
    | x :: xs =>
      let some c := (← get').elimEqs[x]!
        | throwError "`grind` internal error, eliminated variable must have equation associated with it"
      -- `x` may not be the max variable
      let a := c.p.coeff x
      if a == 0 then c.throwUnexpected
      -- ensure `x` is 0 when evaluating `c.p`
      modify' fun s => { s with assignment := s.assignment.set x 0 }
      let some v ← c.p.eval? | c.throwUnexpected
      let v := (-v) / a
      traceAssignment x v
      modify' fun s => { s with assignment := s.assignment.set x v }
      go xs

/--
Tightens `c` using the divisibility constraints of the variables occurring in `c.p`.
For a variable `z` with coefficient `a` in `c.p` and constraint `d ∣ p'` where `p'` has leading
coefficient `±1` on `z`, let `r := c.p - t*p'` with `t := a / (±1)`, and `g` be the gcd of `d`
and the variable coefficients of `r`. If `g > 1`, the value of `c.p` is congruent to the constant
of `r` modulo `g`, and `c.p ≤ 0` can be strengthened to the largest such value `≤ 0`.
Example: `32768 ∣ x` and `-x + 32768*q + 1 ≤ 0` give `-x + 32768*q + 32768 ≤ 0`.

If `decFreeOnly := true`, only the divisibility constraints of the state saved at the first case
split are used. They do not depend on decisions, so neither does the result.
-/
def tightUsingDvds (c : LeCnstr) (decFreeOnly : Bool) : SearchM LeCnstr := do
  let s ← get'
  let s₀ := (← get).cases[0]? |>.map (·.saved) |>.getD s
  let mut c := c
  let mut p := c.p
  repeat
    let .add a z p' := p | break
    p := p'
    -- `z` may have been created after the snapshot was taken.
    let dvd₀? := s₀.dvds[z]?.bind id
    if let some dvd₀ := dvd₀? then
      if let some c' := tighten c a dvd₀ then
        c := c'
    unless decFreeOnly do
      if let some dvd := s.dvds[z]! then
        if dvd₀?.all fun dvd₀ => dvd₀.d != dvd.d || dvd₀.p != dvd.p then
          if let some c' := tighten c a dvd then
            c := c'
  return c
where
  tighten (c : LeCnstr) (a : Int) (dvd : DvdCnstr) : Option LeCnstr := do
    let .add lead _ _ := dvd.p | none
    guard (lead.natAbs == 1)
    let t := a * lead
    let r := c.p.combine (dvd.p.mul (-t))
    let g := r.gcdCoeffs dvd.d.natAbs
    guard (g > 1)
    let shift := -(Int.Internal.Linear.cmod r.getConst g)
    guard (shift != 0)
    return { p := c.p.addConst shift, h := .dvdTightMod dvd c t g }

/--
Best bound for a variable. `val` and `c` use all divisibility constraints for tightening,
`val₀` and `c₀` only those that do not depend on decisions. Conflicts are explained with
`c₀` whenever possible, so that they do not depend on the current case: the untightened bound
often refutes all cases of a Cooper split at once.
-/
structure Bound where
  val  : Rat
  c    : LeCnstr
  val₀ : Rat
  c₀   : LeCnstr

private def Bound.update (b? : Option Bound) (val : Rat) (c : LeCnstr) (val₀ : Rat) (c₀ : LeCnstr) (better : Rat → Rat → Bool) : Option Bound :=
  match b? with
  | none => some { val, c, val₀, c₀ }
  | some b =>
    let b := if better val b.val then { b with val, c } else b
    let b := if better val₀ b.val₀ then { b with val₀, c₀ } else b
    some b

private def evalBound (c : LeCnstr) (lower : Bool) : GoalM Rat := do
  let .add k _ p := c.p | c.throwUnexpected
  let some v ← p.eval? | c.throwUnexpected
  return if lower then v / (-k) else (-v) / k

/--
Assuming all variables smaller than `x` have already been assigned,
returns the best lower bound for `x` using the given partial assignment and
inequality constraints where `x` is the maximal variable.
-/
def getBestLower? (x : Var) : SearchM (Option Bound) := do
  let mut best? := none
  for c in (← get').lowers[x]! do
    let c' ← tightUsingDvds c (decFreeOnly := false)
    let c₀ ← tightUsingDvds c (decFreeOnly := true)
    best? := Bound.update best? (← evalBound c' true) c' (← evalBound c₀ true) c₀ (· > ·)
  return best?

/--
Assuming all variables smaller than `x` have already been assigned,
returns the best upper bound for `x` using the given partial assignment and
inequality constraints where `x` is the maximal variable.
-/
def getBestUpper? (x : Var) : SearchM (Option Bound) := do
  let mut best? := none
  for c in (← get').uppers[x]! do
    let c' ← tightUsingDvds c (decFreeOnly := false)
    let c₀ ← tightUsingDvds c (decFreeOnly := true)
    best? := Bound.update best? (← evalBound c' false) c' (← evalBound c₀ false) c₀ (· < ·)
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
        r := r.push ((-v)/k, c)
  return r

/--
Solution space for a divisibility constraint of the form `d ∣ a*x + b`
See `DvdCnstr.getSolutions` to understand how it is computed.
-/
structure DvdSolution where
  d : Int := 1
  b : Int := 0

inductive DvdSolutionResult where
  | found (s : DvdSolution)
  | /-- The constraint has no solution. -/
    unsat
  | /--
    The constraint cannot be used because the current (rational) assignment makes its
    tail non-integer. The model has been marked as imprecise.
    -/
    skip

def DvdCnstr.getSolutions (c : DvdCnstr) : SearchM DvdSolutionResult := do
  let d := c.d
  let .add a _ p := c.p | c.throwUnexpected
  let some b ← p.eval? | c.throwUnexpected
  if b.den != 1 then
    setImprecise
    return .skip
  let b := b.num
  -- We must solve `d ∣ a*x + b`
  let g := d.gcd a
  if b % g != 0 then
    return .unsat
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
  return .found { d, b := -b*a' }

def resolveDvdConflict (c : DvdCnstr) : GoalM Unit := do
  trace[grind.debug.lia.search.conflict] "{← c.pp}"
  let d := c.d
  let .add a _ p := c.p | c.throwUnexpected
  { d := a.gcd d, p, h := .elim c : DvdCnstr }.assert

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
  (Int.Internal.Linear.cdiv (v - s.b) s.d)*s.d + s.b

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
    leAvoiding s (v-1) dvals
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
  trace[grind.debug.lia.search.conflict] "{← c₁.pp}, {← c₂.pp}"
  let .add a₁ _ p₁ := c₁.p | c₁.throwUnexpected
  let .add a₂ _ p₂ := c₂.p | c₂.throwUnexpected
  let p := p₁.mul a₂.natAbs |>.combine (p₂.mul a₁.natAbs)
  if (← p.satisfiedLe) != .false then
    trace[grind.lia.conflict] "not resolved"
    return false
  else
    let k := p.gcdCoeffs'
    let c := if k == 1 then
      { p, h := .combine c₁ c₂ : LeCnstr }
    else
      { p := p.div k, h := .combineDivCoeffs c₁ c₂ k : LeCnstr }
    trace[grind.debug.lia.search.conflict] "resolved: {← c.pp}"
    c.assert
    return true

def resolveCooperUnary (pred : CooperSplitPred) : SearchM Bool := do
  let some c₃ := pred.c₃? | return false
  let .add (-1) _ (.num a) := pred.c₁.p | return false
  let .add 1 _ (.num b) := pred.c₂.p | return false
  let .add c _ (.num e) := c₃.p | return false
  let d := c₃.d
  let (1, α, _) := gcdExt c d | return false
  unless -b < Int.Internal.Linear.cdiv (a - -α * e % d) d * d + -α * e % d do
    return false
  setInconsistent (.cooper pred.c₁ pred.c₂ c₃)
  return true

def resolveCooperPred (pred : CooperSplitPred) : SearchM Unit := do
  trace[grind.debug.lia.search.conflict] "[{pred.numCases}]: {← pred.pp}"
  if (← resolveCooperUnary pred) then
    return
  let n := pred.numCases
  if n > (← getConfig).liaReorderCases then
    let .add _ x _ := pred.c₁.p | pred.c₁.throwUnexpected
    if (← requestReorder x) then
      return
  let fvarId ← mkCase (.cooper pred #[] {})
  { pred, k := n - 1, h := .dec fvarId : CooperSplit }.assert

def resolveCooper (c₁ c₂ : LeCnstr) : SearchM Unit := do
  let left : Bool := c₁.p.leadCoeff.natAbs < c₂.p.leadCoeff.natAbs
  resolveCooperPred { c₁, c₂, left, c₃? := none }

def resolveCooperDvd (c₁ c₂ : LeCnstr) (c₃ : DvdCnstr) : SearchM Unit := do
  let left : Bool := c₁.p.leadCoeff.natAbs < c₂.p.leadCoeff.natAbs
  resolveCooperPred { c₁, c₂, left, c₃? := some c₃ }

def DiseqCnstr.split (c : DiseqCnstr) : SearchM LeCnstr := do
  let fvarId ← if let some fvarId := (← get').diseqSplits.find? c.p then
    trace[grind.debug.lia.search.split] "{← c.pp}, reusing {fvarId.name}"
    pure fvarId
  else
    let fvarId ← mkCase (.diseq c)
    trace[grind.debug.lia.search.split] "{← c.pp}, {fvarId.name}"
    modify' fun s => { s with diseqSplits := s.diseqSplits.insert c.p fvarId }
    pure fvarId
  let p₂ := c.p.addConst 1
  return { p := p₂, h := .dec fvarId }

/--
Given `c₁` of the form `a₁*x + p₁ ≠ 0`, and `c₂` of the form `b*x + p ≤ 0`
splits `c₁` and resolve with `c₂`.
-/
def resolveCooperDiseq (c₁ : DiseqCnstr) (c₂ : LeCnstr) (c₃? : Option DvdCnstr) : SearchM Unit := do
  -- Ensure the coefficient is positive
  let c₁ := if c₁.p.leadCoeff > 0 then
    { p := c₁.p.mul (-1), h := .neg c₁ : DiseqCnstr }
  else
    c₁
  let c₁ ← c₁.split
  -- After the `c₁.split`, the real shadow may resolve the conflict
  if (← resolveRealLowerUpperConflict c₁ c₂) then
    return ()
  if let some c₃ := c₃? then
    resolveCooperDvd c₁ c₂ c₃
  else
    resolveCooper c₁ c₂

/--
Given `c₁` of the form `-a₁*x + p₁ ≤ 0`, and `c` of the form `b*x + p ≠ 0`,
splits `c` and resolve with `c₁`.
-/
def resolveRatDiseq (c₁ : LeCnstr) (c : DiseqCnstr) : SearchM Unit := do
  let c := if c.p.leadCoeff < 0 then
    { p := c.p.mul (-1), h := .neg c : DiseqCnstr }
  else
    c
  let c₂ ← c.split
  let b ← resolveRealLowerUpperConflict c₁ c₂
  assert! b

def processVar (x : Var) : SearchM Unit := do
  if (← eliminated x) then
    trace[grind.debug.lia.search] "eliminated: {← getVar x}"
    /-
    Variable has been eliminated, and will be assigned later after we have assigned
    variables that have not been eliminated.
    -/
    skipAssignment x
    return ()
  -- Solution space for divisibility constraint is `x = k*d + b`
  let dvd? := (← get').dvds[x]!
  let dvdSol ← if let some c := dvd? then
    match (← c.getSolutions) with
    | .found solutions => pure solutions
    | .skip => pure {}
    | .unsat =>
      if (← isApprox) && !(← get).precise then
        /-
        Some variable was assigned a value that ignores one of its constraints, so the
        resolvent may already be present and resolving would not make progress.
        The `.int` search handles the conflict.
        -/
        pure {}
      else
        trace[grind.debug.lia.search] "dvd conflict: {← c.pp}"
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
  | some lo, none =>
    let lower := lo.val.ceil
    let v := dvdSol.geAvoiding lower diseqVals
    trace[grind.debug.lia.search] "{lower} ≤ {quoteIfArithTerm (← getVar x)} := {v}"
    setAssignment x v
  | none, some up =>
    let upper := up.val.floor
    let v := dvdSol.leAvoiding upper diseqVals
    trace[grind.debug.lia.search] "{quoteIfArithTerm (← getVar x)} := {v} ≤ {upper}"
    setAssignment x v
  | some lo, some up =>
    let lower := lo.val
    let upper := up.val
    let c₁ := lo.c
    let c₂ := up.c
    trace[grind.debug.lia.search] "{lower} ≤ {lower.ceil} ≤ {quoteIfArithTerm (← getVar x)} ≤ {upper.floor} ≤ {upper}"
    if lower > upper then
      -- Prefer the explanation that does not depend on decisions.
      let (c₁, c₂) := if lo.val₀ > up.val₀ then (lo.c₀, up.c₀) else (c₁, c₂)
      let .true ← resolveRealLowerUpperConflict c₁ c₂
        | throwError "`grind` internal error, conflict resolution failed"
      return ()
    -- `lower ≤ upper` here
    if lower.ceil > upper.floor then
      if (← resolveRealLowerUpperConflict lo.c₀ up.c₀) then
        return ()
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
      setImprecise
      if lower < upper then
        setAssignment x <| findRatVal lower upper diseqVals
      else if let some c := findRatDiseq? lower diseqVals then
        resolveRatDiseq c₁ c
      else
        setAssignment x lower
    else
      match r with
      | .dvd => resolveCooperDvd c₁ c₂ dvd?.get!
      | .diseq c => resolveCooperDiseq c c₂ dvd?
      | _ => unreachable!

/-- Returns `true` if we already have a complete assignment / model. -/
def hasAssignment : GoalM Bool := do
  return (← get').vars.size == (← get').assignment.size

private def findCase (decVars : FVarIdSet) : SearchM Case := do
  repeat
    let numCases := (← get).cases.size
    assert! numCases > 0
    let case := (← get).cases[numCases-1]!
    modify fun s => { s with cases := s.cases.pop }
    if decVars.contains case.fvarId then
      return case
    -- Conflict does not depend on this case.
    trace[grind.debug.lia.search.backtrack] "skipping {case.fvarId.name}"
  unreachable!

def resolveConflict (h : UnsatProof) : SearchM Unit := do
  trace[grind.debug.lia.search.backtrack] "resolve conflict, decision stack: {(← get).cases.toList.map fun c => c.fvarId.name}"
  let decVars := h.collectDecVars.run (← get).decVars
  trace[grind.debug.lia.search.backtrack] "dec vars: {decVars.toList.map (·.name)}"
  if decVars.isEmpty then
    trace[grind.debug.lia.search.backtrack] "close goal: {← h.pp}"
    closeGoal (← h.toExprProof)
    return ()
  let c ← findCase decVars
  modify' fun _  => c.saved
  trace[grind.debug.lia.search.backtrack] "backtracking {c.fvarId.name}"
  let decVars := decVars.erase c.fvarId
  match c.kind with
  | .diseq c₁ =>
    let decVars := decVars.toArray
    let p' := c₁.p.mul (-1) |>.addConst 1
    let c' := { p := p', h := .ofDiseqSplit c₁ c.fvarId h decVars : LeCnstr }
    trace[grind.debug.lia.search.backtrack] "resolved diseq split: {← c'.pp}"
    c'.assert
  | .cooper pred hs decVars' =>
    let decVars' := decVars.merge decVars'
    let n := pred.numCases
    let hs := hs.push (c.fvarId, h)
    trace[grind.debug.lia.search.backtrack] "cooper #{hs.size + 1}, {← pred.pp}, {hs.map fun p => p.1.name}"
    let s ← if hs.size + 1 < n then
      let fvarId ← mkCase (.cooper pred hs decVars')
      pure { pred, k := n - hs.size - 1, h := .dec fvarId : CooperSplit }
    else
      let decVars' := decVars'.toArray
      trace[grind.debug.lia.search.backtrack] "cooper last case, {← pred.pp}, dec vars: {decVars'.map (·.name)}"
      pure { pred, k := 0, h := .last hs decVars' : CooperSplit }
    s.assert

/-- Search for an assignment/model for the linear constraints. -/
private def searchAssignmentMain : SearchM Unit := do
  repeat
    trace[grind.debug.lia.search] "main loop"
    checkSystem "cutsat"
    if (← get).reorderRequest?.isSome then
      return ()
    if (← hasAssignment) then
      return ()
    if (← isInconsistent) then
      -- `grind` state is inconsistent
      return ()
    if let some c := (← get').conflict? then
      resolveConflict c
      /-
      Resolving a conflict is a step too. The next case of a Cooper or disequality split may be
      refuted as soon as it is asserted, so a long enumeration never reaches `processVar`.
      We only interrupt below a decision because `resetDecisionStack` then discards the possibly
      pending `conflict?` together with the cases. At level zero, the next iteration resolves it.
      -/
      if (← (return !(← get).cases.isEmpty) <&&> checkMaxSteps) then
        trace[grind.debug.lia.search] "search interrupted, maximum number of steps reached"
        setImprecise
        return ()
    else if (← checkMaxSteps) then
      trace[grind.debug.lia.search] "search interrupted, maximum number of steps reached"
      setImprecise
      return ()
    else
      let x : Var := (← get').assignment.size
      trace[grind.debug.lia.search] "next var: {← getVar x}, {x}, {(← get').assignment.toList}"
      processVar x

private def resetDecisionStack : SearchM Unit := do
  if (← get).cases.isEmpty then
    -- Nothing to reset
    return ()
  -- Backtrack changes but keep the assignment. Variables created during the search
  -- (e.g., by nonlinear term propagation) are rolled back, so their values are dropped.
  let first := (← get).cases[0]!
  modify' fun s => { first.saved with assignment := shrink s.assignment first.saved.vars.size }

private def searchQLiaAssignment : GoalM Bool := do
  let go : SearchM Bool := do
    searchAssignmentMain
    let precise := (← get).precise
    resetDecisionStack
    saveSteps
    return precise
  go .rat |>.run' {}

private def traceActiveCnstrs : GoalM Unit := do
  unless (← isTracingEnabledFor `grind.debug.lia.search.cnstrs) do return ()
  let s ← get'
  for x in [: s.vars.size] do
    unless (← eliminated x) do
      if let some dvd := s.dvds[x]! then
        trace[grind.debug.lia.search.cnstrs] "{← dvd.pp}"
      for c in s.lowers[x]! do
        trace[grind.debug.lia.search.cnstrs] "{← c.pp}"
      for c in s.uppers[x]! do
        trace[grind.debug.lia.search.cnstrs] "{← c.pp}"
      for c in s.diseqs[x]! do
        trace[grind.debug.lia.search.cnstrs] "{← c.pp}"

private def searchLiaAssignment : GoalM Unit := do
  let go : SearchM Bool := do
    searchAssignmentMain
    resetDecisionStack
    saveSteps
    saveReorderRequest
  traceActiveCnstrs
  reorderVars
  traceActiveCnstrs
  repeat
    let requested ← go .int |>.run' {}
    unless requested do return
    trace[grind.debug.lia.search] "restart after reordering request #{(← get').numReorderRequests}"
    modify' fun s => { s with assignment := {} }
    reorderVars (force := true)
    traceActiveCnstrs

def searchAssignment : GoalM Unit := do
  let precise ← searchQLiaAssignment
  if (← isInconsistent) then return ()
  if !(← getConfig).qlia && !precise then
    -- Search for a new model using `.int` mode.
    trace[grind.debug.lia.search] "restart using Cooper resolution"
    modify' fun s => { s with assignment := {} }
    searchLiaAssignment
    trace[grind.debug.lia.search] "after search int model, inconsistent: {← isInconsistent}"
    if (← isInconsistent) then return ()
  -- If the search was interrupted (`liaSteps` threshold), the assignment is partial.
  unless (← hasAssignment) do return ()
  -- TODO: constructing a model is only worth if `grind` will **not** continue searching.
  assignElimVars

/--
Returns `true` if work/progress has been done.
There are two kinds of progress:
- An assignment for satisfying constraints was constructed.
- An inconsistency was detected.

The result is `false` if module already has a satisfying assignment.
-/
def check : GoalM Bool := do profileitM Exception "grind cutsat" (← getOptions) do
  if (← hasAssignment) then
    return false
  else if (← get').steps ≥ (← getConfig).liaSteps then
    -- A previous search reached the `liaSteps` threshold. The solver is disabled to
    -- ensure `grind` does not keep restarting the (bounded) search at every iteration.
    return false
  else
    searchAssignment
    return true

end Lean.Meta.Grind.Arith.Cutsat
