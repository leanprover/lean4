/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Util
import Lean.Meta.Tactic.Grind.AC.DenoteExpr
import Lean.Meta.Tactic.Grind.AC.Proof
import Lean.Meta.Tactic.Grind.AC.Seq
import Lean.Meta.Tactic.Grind.AC.Inv
public section
namespace Lean.Meta.Grind.AC
open Lean.Grind

/-- For each structure `s` s.t. `a` and `b` are elements of, execute `k` -/
@[specialize] def withExprs (a b : Expr) (k : ACM Unit) : GoalM Unit := do
  let ids₁ ← getTermOpIds a
  if ids₁.isEmpty then return ()
  let ids₂ ← getTermOpIds b
  go ids₁ ids₂
where
  go : List Nat → List Nat → GoalM Unit
    | [], _ => return ()
    | _, [] => return ()
    | id₁::ids₁, id₂::ids₂ => do
      if id₁ == id₂ then
        ACM.run id₁ k; go ids₁ ids₂
      else if id₁ < id₂ then
        go ids₁ (id₂::ids₂)
      else
        go (id₁::ids₁) ids₂

def asACExpr (e : Expr) : ACM AC.Expr := do
  if let some e' := (← getStruct).denote.find? { expr := e } then
    return e'
  else
    return .var ((← getStruct).varMap.find? { expr := e }).get!

def norm (e : AC.Expr) : ACM AC.Seq := do
  match (← isCommutative), (← hasNeutral) with
  | true,  true  => return e.toSeq.erase0.sort
  | true,  false => return e.toSeq.sort
  | false, true  => return e.toSeq.erase0
  | false, false => return e.toSeq

/--
Returns `some (c, r)`, where `c` is an equation from the basis whose LHS simplifies `s` when
`(← isCommutative)` is `false`
-/
private def _root_.Lean.Grind.AC.Seq.findSimpA? (s : AC.Seq) : ACM (Option (EqCnstr × AC.SubseqResult)) := do
  for c in (← getStruct).basis do
    let r := c.lhs.subseq s
    unless r matches .false do return some (c, r)
  return none

/--
Returns `some (c, r)`, where `c` is an equation from the basis whose LHS simplifies `s` when
`(← isCommutative)` is `true`
-/
private def _root_.Lean.Grind.AC.Seq.findSimpAC? (s : AC.Seq) : ACM (Option (EqCnstr × AC.SubsetResult)) := do
  for c in (← getStruct).basis do
    let r := c.lhs.subset s
    unless r matches .false do return some (c, r)
  return none

local macro "gen_cnstr_fns " cnstr:ident : command =>
  let mkId (declName : Name) := mkIdent <| cnstr.getId ++ declName
  `(
  private def $(mkId `eraseDup) (c : $cnstr) : ACM $cnstr := do
    unless (← isIdempotent) do return c
    let lhs := c.lhs.eraseDup
    let rhs := c.rhs.eraseDup
    if c.lhs == lhs && c.rhs == rhs then
      return c
    else
      return { c with lhs, rhs, h := .erase_dup c }

  private def $(mkId `erase0) (c : $cnstr) : ACM $cnstr := do
    unless (← hasNeutral) do return c
    let lhs := c.lhs.erase0
    let rhs := c.rhs.erase0
    if c.lhs == lhs && c.rhs == rhs then
      return c
    else
      return { c with lhs, rhs, h := .erase0 c }

  private def $(mkId `cleanup) (c : $cnstr) : ACM $cnstr := do
    (← c.eraseDup).erase0

  private def $(mkId `simplifyLhsWithA) (c : $cnstr) (c' : EqCnstr) (r : AC.SubseqResult) : $cnstr :=
    match r with
    | .exact    => { c with lhs := c'.rhs, h := .simp_exact (lhs := true) c' c }
    | .prefix s => { c with lhs := c'.rhs ++ s, h := .simp_prefix (lhs := true) s c' c }
    | .suffix s => { c with lhs := s ++ c'.rhs, h := .simp_suffix (lhs := true) s c' c }
    | .middle p s => { c with lhs := p ++ c'.rhs ++ s, h := .simp_middle (lhs := true) p s c' c }
    | .false => c

  private def $(mkId `simplifyRhsWithA) (c : $cnstr) (c' : EqCnstr) (r : AC.SubseqResult) : $cnstr :=
    match r with
    | .exact    => { c with rhs := c'.rhs, h := .simp_exact (lhs := false) c' c }
    | .prefix s => { c with rhs := c'.rhs ++ s, h := .simp_prefix (lhs := false) s c' c }
    | .suffix s => { c with rhs := s ++ c'.rhs, h := .simp_suffix (lhs := false) s c' c }
    | .middle p s => { c with rhs := p ++ c'.rhs ++ s, h := .simp_middle (lhs := false) p s c' c }
    | .false => c

  /-- Simplifies `c` using the basis when `(← isCommutative)` is `false` -/
  private def $(mkId `simplifyA) (c : $cnstr) : ACM $cnstr := do
    let mut c ← c.cleanup
    repeat
      incSteps
      if (← checkMaxSteps) then return c
      if let some (c', r) ← c.lhs.findSimpA? then
        c := c.simplifyLhsWithA c' r
        c ← c.cleanup
      else if let some (c', r) ← c.rhs.findSimpA? then
        c := c.simplifyRhsWithA c' r
        c ← c.cleanup
      else
        trace[grind.debug.ac.simplify] "{← c.denoteExpr}"
        return c
    return c

  /--
  Simplifies `c` (lhs and rhs) using `c'`, returns `some c` if simplified.
  Case `(← isCommutative) == false`
  -/
  private def $(mkId `simplifyWithA') (c : $cnstr) (c' : EqCnstr) : Option $cnstr := do
    let r₁ := c'.lhs.subseq c.lhs
    let c := c.simplifyLhsWithA c' r₁
    let r₂ := c'.lhs.subseq c.rhs
    let c := c.simplifyRhsWithA c' r₂
    if r₁ matches .false && r₂ matches .false then none else some c

  private def $(mkId `simplifyLhsWithAC) (c : $cnstr) (c' : EqCnstr) (r : AC.SubsetResult) : $cnstr :=
    match r with
    | .exact    => { c with lhs := c'.rhs, h := .simp_exact (lhs := true) c' c }
    | .strict s => { c with lhs := c'.rhs.union s, h := .simp_ac (lhs := true) s c' c }
    | .false => c

  private def $(mkId `simplifyRhsWithAC) (c : $cnstr) (c' : EqCnstr) (r : AC.SubsetResult) : $cnstr :=
    match r with
    | .exact    => { c with rhs := c'.rhs, h := .simp_exact (lhs := false) c' c }
    | .strict s => { c with rhs := c'.rhs.union s, h := .simp_ac (lhs := false) s c' c }
    | .false => c

  /--
  Simplifies `c` (lhs and rhs) using `c'`, returns `some c` if simplified.
  Case `(← isCommutative) == true`
  -/
  private def $(mkId `simplifyWithAC') (c : $cnstr) (c' : EqCnstr) : Option $cnstr := do
    let r₁ := c'.lhs.subset c.lhs
    let c := c.simplifyLhsWithAC c' r₁
    let r₂ := c'.lhs.subset c.rhs
    let c := c.simplifyRhsWithAC c' r₂
    if r₁ matches .false && r₂ matches .false then none else some c

  /-- Simplify `c` using the basis when `(← isCommutative)` is `true` -/
  private def $(mkId `simplifyAC) (c : $cnstr) : ACM $cnstr := do
    let mut c ← c.cleanup
    repeat
      incSteps
      trace[grind.debug.ac.simp] "{← c.denoteExpr}"
      if (← checkMaxSteps) then return c
      if let some (c', r) ← c.lhs.findSimpAC? then
        c := c.simplifyLhsWithAC c' r
        c ← c.cleanup
      else if let some (c', r) ← c.rhs.findSimpAC? then
        c := c.simplifyRhsWithAC c' r
        c ← c.cleanup
      else
        trace[grind.debug.ac.simp] "done: {← c.denoteExpr}"
        return c
    return c

  /--
  Simplifies `c` (lhs and rhs) using `c'`, returns `some c` if simplified.
  -/
  private def $(mkId `simplifyWith) (c : $cnstr) (c' : EqCnstr) : ACM (Option $cnstr) := do
    incSteps
    if (← isCommutative) then
      return c.simplifyWithAC' c'
    else
      return c.simplifyWithA' c'

  /-- Simplify `c` using the basis -/
  private def $(mkId `simplify) (c : $cnstr) : ACM $cnstr := do
    if (← isCommutative) then c.simplifyAC else c.simplifyA
)

gen_cnstr_fns EqCnstr
gen_cnstr_fns DiseqCnstr

private def saveDiseq (c : DiseqCnstr) : ACM Unit := do
  modifyStruct fun s => { s with diseqs := s.diseqs.push c }

private def DiseqCnstr.assert (c : DiseqCnstr) : ACM Unit := do
  let c ← c.eraseDup
  let c ← c.simplify
  trace[grind.ac.assert] "{← c.denoteExpr}"
  if c.lhs == c.rhs then
    c.setUnsat
  else
    saveDiseq c

private def mkEqCnstr (lhs rhs : AC.Seq) (h : EqCnstrProof) : ACM EqCnstr := do
  let id := (← getStruct).nextId
  modifyStruct fun s => { s with nextId := s.nextId + 1 }
  return { lhs, rhs, h, id }

private def EqCnstr.orient (c : EqCnstr) : EqCnstr :=
  if compare c.rhs c.lhs == .gt then
    { c with lhs := c.rhs, rhs := c.lhs, h := .swap c }
  else
    c

private def EqCnstr.addToQueue (c : EqCnstr) : ACM Unit := do
  trace[grind.debug.ac.queue] "{← c.denoteExpr}"
  modifyStruct fun s => { s with queue := s.queue.insert c }

private def EqCnstr.superposeWithAC (c₁ : EqCnstr) : ACM Unit := do
  if (← checkMaxSteps) then return ()
  let lhs₁ := c₁.lhs
  for c₂ in (← getStruct).basis do
    let lhs₂ := c₂.lhs
    trace[grind.debug.ac.superpose] "[{lhs₁.sharesVar lhs₂}]: {← lhs₁.denoteExpr}, {← lhs₂.denoteExpr}"
    if lhs₁.sharesVar lhs₂ then
      assert! lhs₁ != lhs₂
      let some (r₁, c, r₂) := lhs₁.superposeAC? lhs₂ | unreachable!
      if grind.debug.get (← getOptions) then
        assert! lhs₁ == r₁.union c
        assert! lhs₂ == r₂.union c
      let c ← mkEqCnstr (c₁.rhs.union r₂) (c₂.rhs.union r₁) (.superpose_ac r₁ c r₂ c₁ c₂)
      c.addToQueue

private def EqCnstr.superposeA (c₁ c₂ : EqCnstr) : ACM Unit := do
  let lhs₁ := c₁.lhs
  let lhs₂ := c₂.lhs
  assert! lhs₁ != lhs₂
  if let some (p, c, s) := lhs₁.superpose? lhs₂ then
    if grind.debug.get (← getOptions) then
      assert! lhs₁ == p ++ c
      assert! lhs₂ == c ++ s
    let c ← mkEqCnstr (c₁.rhs ++ s) (p ++ c₂.rhs) (.superpose p c s c₁ c₂)
    c.addToQueue

private def EqCnstr.superposeWithA (c₁ : EqCnstr) : ACM Unit := do
  if (← checkMaxSteps) then return ()
  let lhs₁ := c₁.lhs
  for c₂ in (← getStruct).basis do
    let lhs₂ := c₂.lhs
    if lhs₁.sharesVar lhs₂ then
      c₁.superposeA c₂
      c₂.superposeA c₁

/--
If the operator is idempotent, we have to add extra critical pairs.
See section 4.1 of the paper "MODULARITY, COMBINATION, AC CONGRUENCE CLOSURE"
The idea is the following, given `c` of the form `lhs = rhs`,
for each variable `x` in `lhs` s.t. `x` is not in `rhs`, we add the equation
`lhs = rhs.union {x}`
Note that the paper does not include `x` is not in `rhs`, but this extra filter is correct
since after normalization and simplification `lhs = rhs.union {x}` would be discarded.
-/
private def EqCnstr.superposeAC_Idempotent (c : EqCnstr) : ACM Unit := do
  go c.lhs
where
  goVar (x : AC.Var) : ACM Unit := do
    unless c.rhs.contains x do
      let c := { c with rhs := c.rhs.insert x, h := .superpose_ac_idempotent x c }
      if (← hasNeutral) && c.rhs.contains 0 then
        (← c.erase0).addToQueue
      else
        c.addToQueue

  go (s : AC.Seq) : ACM Unit := do
    match s with
    | .var x => goVar x
    | .cons x s => goVar x; go s

private def EqCnstr.superposeWith (c : EqCnstr) : ACM Unit := do
  if (← isCommutative) then
    c.superposeWithAC
    if (← isIdempotent) then c.superposeAC_Idempotent
  else
    c.superposeWithA

private def EqCnstr.simplifyBasis (c : EqCnstr) : ACM Unit := do
  let rec go (basis : List EqCnstr) (acc : List EqCnstr) : ACM (List EqCnstr) := do
    match basis with
    | [] => return acc.reverse
    | c' :: basis =>
      if let some c'' ← c'.simplifyWith c then
        trace[grind.debug.ac.simp] "{← c'.denoteExpr} using {← c.denoteExpr} := {← c''.denoteExpr}"
        c''.addToQueue
        go basis acc
      else
        go basis (c' :: acc)
  let basis ← go (← getStruct).basis []
  modifyStruct fun s => { s with basis }

private def addSorted (c : EqCnstr) : List EqCnstr → List EqCnstr
  | [] => [c]
  | c' :: cs =>
    if c.lhs.length ≤ c'.lhs.length then
      c :: c' :: cs
    else
      c' :: addSorted c cs

private def EqCnstr.addToBasisCore (c : EqCnstr) : ACM Unit := do
  trace[grind.ac.basis] "{← c.lhs.denoteExpr} ↝ {← c.rhs.denoteExpr}"
  modifyStruct fun s => { s with
    basis := addSorted c s.basis
    recheck := true
  }

private def EqCnstr.addToBasisAfterSimp (c : EqCnstr) : ACM Unit := do
  c.simplifyBasis
  c.superposeWith
  addToBasisCore c

private def EqCnstr.addToBasis (c : EqCnstr) : ACM Unit := do
  let c ← c.simplify
  if c.lhs == c.rhs then return ()
  let c := c.orient
  c.addToBasisAfterSimp

private def EqCnstr.assert (c : EqCnstr) : ACM Unit := do
  let c ← c.simplify
  if c.lhs == c.rhs then return ()
  let c := c.orient
  trace[grind.ac.assert] "{← c.denoteExpr}"
  if c.lhs.isVar then
    c.addToBasisAfterSimp
  else
    c.addToQueue

@[export lean_process_ac_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := withExprs a b do
  let ea ← asACExpr a
  let lhs ← norm ea
  let eb ← asACExpr b
  let rhs ← norm eb
  let c ← mkEqCnstr lhs rhs (.core a b ea eb)
  c.assert

@[export lean_process_ac_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := withExprs a b do
  let ea ← asACExpr a
  let lhs ← norm ea
  let eb ← asACExpr b
  let rhs ← norm eb
  { lhs, rhs, h := .core a b ea eb : DiseqCnstr }.assert

private def isQueueEmpty : ACM Bool :=
  return (← getStruct).queue.isEmpty

/--
Returns `true` if the todo queue is not empty or the `recheck` flag is set to `true`
-/
private def needCheck : ACM Bool := do
  unless (← isQueueEmpty) do return true
  return (← getStruct).recheck

private def getNext? : ACM (Option EqCnstr) := do
  let some c := (← getStruct).queue.min? | return none
  modifyStruct fun s => { s with queue := s.queue.erase c }
  incSteps
  return some c

private def checkDiseqs : ACM Unit := do
  let diseqs := (← getStruct).diseqs
  modifyStruct fun s => { s with diseqs := {} }
  for c in diseqs do
    c.assert
    if (← isInconsistent) then return

private def propagateEqs : ACM Unit := do
  -- TODO
  return ()

private def checkStruct : ACM Bool := do
  unless (← needCheck) do return false
  trace_goal[grind.debug.ac.check] "{(← getStruct).op}"
  repeat
    checkSystem "ac"
    let some c ← getNext? | break
    trace_goal[grind.debug.ac.check] "{← c.denoteExpr}"
    c.addToBasis
    if (← isInconsistent) then return true
    if (← checkMaxSteps) then return true
  checkDiseqs
  propagateEqs
  modifyStruct fun s => { s with recheck := false }
  return true

def check : GoalM Bool := do profileitM Exception "grind ac" (← getOptions) do
  if (← checkMaxSteps) then return false
  let mut progress := false
  checkInvariants
  try
    for opId in *...(← get').structs.size do
      let r ← ACM.run opId checkStruct
      progress := progress || r
      if (← isInconsistent) then return true
    return progress
  finally
    checkInvariants

end Lean.Meta.Grind.AC
