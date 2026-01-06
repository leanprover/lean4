/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.Den
import Lean.Meta.Tactic.Grind.Arith.Linear.Var
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.Proof
import Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule
public section
namespace Lean.Meta.Grind.Arith.Linear

private def _root_.Lean.Grind.Linarith.Poly.substVar (p : Poly) : LinearM (Option (Var × EqCnstr × Poly)) := do
  let some (a, x, c) ← p.findVarToSubst | return none
  let b := c.p.coeff x
  let p' := p.mul b |>.combine (c.p.mul (-a))
  trace[grind.debug.linarith.subst] "{← p.denoteExpr}, {a}, {← getVar x}, {← c.denoteExpr}, {b}, {← p'.denoteExpr}"
  return some (x, c, p')

/--
Given an equation `c₁` containing the monomial `a*x`, and a disequality constraint `c₂`
containing the monomial `b*x`, eliminate `x` by applying substitution.
-/
private def DiseqCnstr.applyEq? (a : Int) (x : Var) (c₁ : EqCnstr) (b : Int) (c₂ : DiseqCnstr) : LinearM (Option DiseqCnstr) := do
  trace[grind.linarith.subst] "{← getVar x}, {← c₁.denoteExpr}, {← c₂.denoteExpr}"
  let p := c₁.p
  let q := c₂.p
  if b % a == 0 then
    let k := - b / a
    let p := p.mul k |>.combine q
    return some { p, h := .subst1 k c₁ c₂ }
  else if (← hasNoNatZeroDivisors) then
    let p := p.mul b |>.combine (q.mul (-a))
    return some { p, h := .subst (-a) b c₁ c₂ }
  else
    return none

/-- Returns `some structId` if `a` and `b` are elements of the same structure. -/
private def inSameStruct? (a b : Expr) : GoalM (Option Nat) := do
  let some structId ← getTermStructId? a | return none
  let some structId' ← getTermStructId? b | return none
  unless structId == structId' do return none -- This can happen when we have heterogeneous equalities
  return structId

private def processNewCommRingEq' (a b : Expr) : LinearM Unit := do
  let some lhs ← withRingM <| CommRing.reify? a (skipVar := false) | return ()
  let some rhs ← withRingM <| CommRing.reify? b (skipVar := false) | return ()
  let generation := max (← getGeneration a) (← getGeneration b)
  let p := (lhs.sub rhs).toPoly
  let c : RingEqCnstr := { p, h := .core a b lhs rhs }
  let c ← c.cleanupDenominators
  let p := c.p
  let lhs ← p.toIntModuleExpr generation
  let some lhs ← reify? lhs (skipVar := false) generation | return ()
  let p := lhs.norm
  if p == .nil then return ()
  let c₁ : IneqCnstr := { p, strict := false, h := .ringEq c lhs }
  c₁.assert
  let c := { c with p := c.p.mulConst (-1), h := .symm c }
  let p := p.mul (-1)
  let lhs ← c.p.toIntModuleExpr generation
  let some lhs ← reify? lhs (skipVar := false) generation | return ()
  let c₂ : IneqCnstr := { p, strict := false, h := .ringEq c lhs }
  c₂.assert

private def processNewIntModuleEq' (a b : Expr) : LinearM Unit := do
  let some lhs ← reify? a (skipVar := false) (← getGeneration a) | return ()
  let some rhs ← reify? b (skipVar := false) (← getGeneration b) | return ()
  let p := (lhs.sub rhs).norm
  if p == .nil then return ()
  let c₁ : IneqCnstr := { p, strict := false, h := .ofEq a b lhs rhs }
  c₁.assert
  let p := p.mul (-1)
  let c₂ : IneqCnstr := { p, strict := false, h := .ofEq b a rhs lhs }
  c₂.assert

private def EqCnstr.norm (c : EqCnstr) : LinearM (Nat × Var × EqCnstr) := do
  let mut c := c
  if (← hasNoNatZeroDivisors) then
    let k := c.p.gcdCoeffs
    if k != 1 then
      c := { p := c.p.div k, h := .coeff k c }
  let some (k, x) := c.p.pickVarToElim? | unreachable!
  if k < 0 then
    c := { p := c.p.mul (-1), h := .neg c }
  return (k.natAbs, x, c)

private partial def EqCnstr.applySubsts (c : EqCnstr) : LinearM EqCnstr := withIncRecDepth do
  let some (x, c₁, p) ← c.p.substVar | return c
  trace[grind.debug.linarith.subst] "{← getVar x}, {← c.denoteExpr}, {← c₁.denoteExpr}"
  applySubsts { p, h := .subst x c₁ c : EqCnstr }

/--
Given an equation `c₁` containing the monomial `a*x`, and an inequality constraint `c₂`
containing the monomial `b*x`, eliminate `x` by applying substitution.
-/
private def IneqCnstr.applyEq (a : Nat) (x : Var) (c₁ : EqCnstr) (b : Int) (c₂ : IneqCnstr) : LinearM IneqCnstr := do
  let p := c₁.p
  let q := c₂.p
  let p := q.mul a |>.combine (p.mul (-b))
  trace[grind.linarith.subst] "{← getVar x}, {← c₁.denoteExpr}, {← c₂.denoteExpr}"
  return { p, h := .subst x c₁ c₂, strict := c₂.strict }

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from the inequalities in `todo`.
`todo` contains pairs of the form `(b, c₂)` where `b` is the coefficient of `x` in `c₂`.
-/
private def updateLeCnstrs (a : Nat) (x : Var) (c₁ : EqCnstr) (todo : Array (Int × IneqCnstr)) : LinearM Unit := do
  for (b, c₂) in todo do
    let c₂ ← c₂.applyEq a x c₁ b
    c₂.assert
    if (← inconsistent) then return ()

private def splitIneqCnstrs (x : Var) (cs : PArray IneqCnstr) : PArray IneqCnstr × Array (Int × IneqCnstr) :=
  split cs fun c => c.p.coeff x

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from lower bound inequalities of `y`.
-/
private def updateLowers (a : Nat) (x : Var) (c : EqCnstr) (y : Var) : LinearM Unit := do
  if (← inconsistent) then return ()
  let (lowers', todo) := splitIneqCnstrs x (← getStruct).lowers[y]!
  modifyStruct fun s => { s with lowers := s.lowers.set y lowers' }
  updateLeCnstrs a x c todo

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from upper bound inequalities of `y`.
-/
private def updateUppers (a : Nat) (x : Var) (c : EqCnstr) (y : Var) : LinearM Unit := do
  if (← inconsistent) then return ()
  let (uppers', todo) := splitIneqCnstrs x (← getStruct).uppers[y]!
  modifyStruct fun s => { s with uppers := s.uppers.set y uppers' }
  updateLeCnstrs a x c todo

private def DiseqCnstr.ignore (c : DiseqCnstr) : LinearM Unit := do
  -- Remark: we filter duplicates before displaying diagnostics to users
  trace[grind.linarith.assert.ignored] "{← c.denoteExpr}"
  let diseq ← c.denoteExpr
  modifyStruct fun s => { s with ignored := s.ignored.push diseq }

partial def DiseqCnstr.applySubsts? (c₂ : DiseqCnstr) : LinearM (Option DiseqCnstr) := withIncRecDepth do
  let some (b, x, c₁) ← c₂.p.findVarToSubst | return some c₂
  let a := c₁.p.coeff x
  if let some c₂ ← c₂.applyEq? a x c₁ b then
    c₂.applySubsts?
  else
    -- Failed to eliminate
    c₂.ignore
    return none

private def DiseqCnstr.assert (c : DiseqCnstr) : LinearM Unit := do
  trace[grind.linarith.assert] "{← c.denoteExpr}"
  let some c ← c.applySubsts? | return ()
  match c.p with
  | .nil =>
    trace[grind.linarith.unsat] "{← c.denoteExpr}"
    setInconsistent (.diseq c)
  | .add _ x _ =>
    trace[grind.linarith.assert.store] "{← c.denoteExpr}"
    c.p.updateOccs
    modifyStruct fun s => { s with diseqs := s.diseqs.modify x (·.push c) }
    if (← c.satisfied) == .false then
      resetAssignmentFrom x

private def splitDiseqs (x : Var) (cs : PArray DiseqCnstr) : PArray DiseqCnstr × Array (Int × DiseqCnstr) :=
  split cs fun c => c.p.coeff x

private def updateDiseqs (a : Int) (x : Var) (c : EqCnstr) (y : Var) : LinearM Unit := do
  if (← inconsistent) then return ()
  let (diseqs', todo) := splitDiseqs x (← getStruct).diseqs[y]!
  modifyStruct fun s => { s with diseqs := s.diseqs.set y diseqs' }
  for (b, c₂) in todo do
    if let some c₂ ← c₂.applyEq? a x c b then
      c₂.assert
      if (← inconsistent) then return ()
    else
      -- Failed to eliminate
      c₂.ignore

private def updateOccsAt (a : Nat) (x : Var) (c : EqCnstr) (y : Var) : LinearM Unit := do
  updateLowers a x c y
  updateUppers a x c y
  updateDiseqs a x c y

private def updateOccs (a : Nat) (x : Var) (c : EqCnstr) : LinearM Unit := do
  let ys := (← getStruct).occurs[x]!
  modifyStruct fun s => { s with occurs := s.occurs.set x {} }
  updateOccsAt a x c x
  for y in ys do
    updateOccsAt a x c y

private def isImpliedEq (c : EqCnstr) : LinearM Bool := do
  match c.p with
  | .add (-1) x (.add 1 y .nil)
  | .add 1 x (.add (-1) y .nil) =>
    if (← isEqv (← getVar x) (← getVar y)) then return false
    return true
  | _ => return false

private def ensureLeadCoeffPos (c : EqCnstr) : LinearM EqCnstr := do
  let .add k _ _ := c.p | return c
  if k < 0 then
    return { p := c.p.mul (-1), h := .neg c }
  else
    return c

private def EqCnstr.assert (c : EqCnstr) : LinearM Unit := do
  trace[grind.linarith.assert] "{← c.denoteExpr}"
  let c ← c.applySubsts
  if c.p == .nil then
    trace[grind.linarith.trivial] "{← c.denoteExpr}"
    return ()
  let (a, x, c) ← c.norm
  trace[grind.debug.linarith.subst] ">> {← getVar x}, {← c.denoteExpr}"
  trace[grind.linarith.assert.store] "{← c.denoteExpr}"
  /-
  **Note**:
  We currently only catch equalities of the form `x + -1*y = 0`
  This is sufficient for catching trivial cases, but to catch all implied equalities
  we need to keep a mapping from `(Poly, Int)` to `Var`. The mapping contains an entry `(p, k) ↦ x`
  if `x` is an eliminated variable and there is a constraint that implies `k*x = p`.
  We need this mapping to catch `k*x = p` and `k*y = p`
  -/
  unless (← getStruct).caseSplits do
    if (← isImpliedEq c) then
      propagateImpEq (← ensureLeadCoeffPos c)
  modifyStruct fun s => { s with
    elimEqs := s.elimEqs.set x (some c)
    elimStack := x :: s.elimStack
  }
  updateOccs a x c

private def processNewCommRingEq (a b : Expr) : LinearM Unit := do
  trace[Meta.debug] "{a}, {b}"
  -- TODO

private def processNewIntModuleEq (a b : Expr) : LinearM Unit := do
  let some lhs ← reify? a (skipVar := false) (← getGeneration a) | return ()
  let some rhs ← reify? b (skipVar := false) (← getGeneration b) | return ()
  let p := (lhs.sub rhs).norm
  if p == .nil then return ()
  let c : EqCnstr := { p, h := .core a b lhs rhs }
  c.assert

private def processNewNatModuleEq' (a b : Expr) : OfNatModuleM Unit := do
  let ns ← getNatStruct
  let (a', _) ← ofNatModule a
  let (b', _) ← ofNatModule b
  LinearM.run ns.structId do
    let some lhs ← reify? a' (skipVar := false) (← getGeneration a) | return ()
    let some rhs ← reify? b' (skipVar := false) (← getGeneration b) | return ()
    let p := (lhs.sub rhs).norm
    if p == .nil then return ()
    let c₁ : IneqCnstr := { p, strict := false, h := .ofEqOfNat a b ns.id lhs rhs }
    c₁.assert
    let p := p.mul (-1)
    let c₂ : IneqCnstr := { p, strict := false, h := .ofEqOfNat b a ns.id rhs lhs }
    c₂.assert

private def processNewNatModuleEq (a b : Expr) : OfNatModuleM Unit := do
  let ns ← getNatStruct
  let (a', _) ← ofNatModule a
  let (b', _) ← ofNatModule b
  LinearM.run ns.structId do
    let some lhs ← reify? a' (skipVar := false) (← getGeneration a) | return ()
    let some rhs ← reify? b' (skipVar := false) (← getGeneration b) | return ()
    let p := (lhs.sub rhs).norm
    if p == .nil then return ()
    let c : EqCnstr := { p, h := .coreOfNat a b ns.id lhs rhs }
    c.assert

def processNewEq (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  if let some structId ← inSameStruct? a b then LinearM.run structId do
    if (← isOrderedAdd) then
      if (← isCommRing) then
        processNewCommRingEq' a b
      else
        processNewIntModuleEq' a b
    else
      if (← isCommRing) then
        processNewCommRingEq a b
      else
        processNewIntModuleEq a b
  else if let some natStructId ← inSameNatStruct? a b then OfNatModuleM.run natStructId do
    let ns ← getNatStruct
    if ns.orderedAddInst?.isSome then
      processNewNatModuleEq' a b
    else
      processNewNatModuleEq a b

private def processNewCommRingDiseq (a b : Expr) : LinearM Unit := do
  let some lhs ← withRingM <| CommRing.reify? a (skipVar := false) | return ()
  let some rhs ← withRingM <| CommRing.reify? b (skipVar := false) | return ()
  let p := (lhs.sub rhs).toPoly
  let c : RingDiseqCnstr := { p, h := .core a b lhs rhs }
  let c ← c.cleanupDenominators
  let p := c.p
  let generation := max (← getGeneration a) (← getGeneration b)
  let lhs ← p.toIntModuleExpr generation
  let some lhs ← reify? lhs (skipVar := false) generation | return ()
  let p := lhs.norm
  let c : DiseqCnstr := { p, h := .ring c lhs }
  c.assert

private def processNewIntModuleDiseq (a b : Expr) : LinearM Unit := do
  let some lhs ← reify? a (skipVar := false) (← getGeneration a) | return ()
  let some rhs ← reify? b (skipVar := false) (← getGeneration b) | return ()
  let p := (lhs.sub rhs).norm
  let c : DiseqCnstr := { p, h := .core a b lhs rhs }
  c.assert

private def processNewNatModuleDiseq (a b : Expr) : OfNatModuleM Unit := do
  let ns ← getNatStruct
  if ns.addRightCancelInst?.isSome then
    let (a', _) ← ofNatModule a
    let (b', _) ← ofNatModule b
    LinearM.run ns.structId do
      let some lhs ← reify? a' (skipVar := false) (← getGeneration a) | return ()
      let some rhs ← reify? b' (skipVar := false) (← getGeneration b) | return ()
      let p := (lhs.sub rhs).norm
      let c : DiseqCnstr := { p, h := .coreOfNat a b ns.id lhs rhs }
      c.assert
  else
    -- If `AddRightCancel` is not available, we just normalize, and try to detect contradiction
    normNatModuleDiseq a b

def processNewDiseq (a b : Expr) : GoalM Unit := do
  if let some structId ← inSameStruct? a b then LinearM.run structId do
    if (← isCommRing) then
      processNewCommRingDiseq a b
    else
      processNewIntModuleDiseq a b
  else if let some natStructId ← inSameNatStruct? a b then OfNatModuleM.run natStructId do
    processNewNatModuleDiseq a b

end Lean.Meta.Grind.Arith.Linear
