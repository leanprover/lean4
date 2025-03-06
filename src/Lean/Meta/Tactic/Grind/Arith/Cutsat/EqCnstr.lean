/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr

namespace Lean.Meta.Grind.Arith.Cutsat

private def _root_.Int.Linear.Poly.substVar (p : Poly) : GoalM (Option (Var × EqCnstr × Poly)) := do
  let some (a, x, c) ← p.findVarToSubst | return none
  let b := c.p.coeff x
  let p' := p.mul (-b) |>.combine (c.p.mul a)
  trace[grind.debug.cutsat.subst] "{← p.pp}, {a}, {← getVar x}, {← c.pp}, {b}, {← p'.pp}"
  return some (x, c, p')

def EqCnstr.norm (c : EqCnstr) : EqCnstr :=
  if c.p.isSorted then
    c
  else
    { p := c.p.norm, h := .norm c }

def DiseqCnstr.norm (c : DiseqCnstr) : DiseqCnstr :=
  if c.p.isSorted then
    c
  else
    { p := c.p.norm, h := .norm c }

/--
Given an equation `c₁` containing the monomial `a*x`, and a disequality constraint `c₂`
containing the monomial `b*x`, eliminate `x` by applying substitution.
-/
def DiseqCnstr.applyEq (a : Int) (x : Var) (c₁ : EqCnstr) (b : Int) (c₂ : DiseqCnstr) : GoalM DiseqCnstr := do
  let p := c₁.p
  let q := c₂.p
  let p := p.mul b |>.combine (q.mul (-a))
  trace[grind.cutsat.subst] "{← getVar x}, {← c₁.pp}, {← c₂.pp}"
  return { p, h := .subst x c₁ c₂ }

partial def DiseqCnstr.applySubsts (c : DiseqCnstr) : GoalM DiseqCnstr := withIncRecDepth do
  let some (x, c₁, p) ← c.p.substVar | return c
  trace[grind.cutsat.subst] "{← getVar x}, {← c.pp}, {← c₁.pp}"
  applySubsts { p, h := .subst x c₁ c }

/--
Given a disequality `c`, tries to find an inequality to be refined using
`p ≤ 0 → p ≠ 0 → p + 1 ≤ 0`
-/
private def DiseqCnstr.findLe (c : DiseqCnstr) : GoalM Bool := do
  let .add _ x _ := c.p | c.throwUnexpected
  let s ← get'
  let go (atLower : Bool) : GoalM Bool := do
    let cs' := if atLower then s.lowers[x]! else s.uppers[x]!
    for c' in cs' do
      if c.p == c'.p || c.p.isNegEq c'.p then
        c'.erase
        { p := c'.p.addConst 1, h := .ofLeDiseq c' c : LeCnstr }.assert
        return true
    return false
  go true <||> go false

def DiseqCnstr.assert (c : DiseqCnstr) : GoalM Unit := do
  if (← inconsistent) then return ()
  trace[grind.cutsat.assert] "{← c.pp}"
  let c ← c.norm.applySubsts
  if c.p.isUnsatDiseq then
    setInconsistent (.diseq c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.diseq.trivial] "{← c.pp}"
    return ()
  let k := c.p.gcdCoeffs c.p.getConst
  let c := if k == 1 then
    c
  else
    { p := c.p.div k, h := .divCoeffs c }
  if (← c.findLe) then
    return ()
  let .add _ x _ := c.p | c.throwUnexpected
  c.p.updateOccs
  trace[grind.cutsat.diseq] "{← c.pp}"
  modify' fun s => { s with diseqs := s.diseqs.modify x (·.push c) }
  if (← c.satisfied) == .false then
    resetAssignmentFrom x

/--
Selects the variable in the given linear polynomial whose coefficient has the smallest absolute value.
-/
def _root_.Int.Linear.Poly.pickVarToElim? (p : Poly) : Option (Int × Var) :=
  match p with
  | .num _ => none
  | .add k x p => go k x p
where
  go (k : Int) (x : Var) (p : Poly) : Int × Var :=
    if k == 1 || k == -1 then
      (k, x)
    else match p with
      | .num _ => (k, x)
      | .add k' x' p =>
        if k'.natAbs < k.natAbs then
          go k' x' p
        else
          go k x p

partial def EqCnstr.applySubsts (c : EqCnstr) : GoalM EqCnstr := withIncRecDepth do
  let some (x, c₁, p) ← c.p.substVar | return c
  trace[grind.cutsat.subst] "{← getVar x}, {← c.pp}, {← c₁.pp}"
  applySubsts { p, h := .subst x c₁ c : EqCnstr }

private def updateDvdCnstr (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  let some c' := (← get').dvds[y]! | return ()
  let b := c'.p.coeff x
  if b == 0 then return ()
  modify' fun s => { s with dvds := s.dvds.set y none }
  let c' ← c'.applyEq a x c b
  c'.assert

private def split (x : Var) (cs : PArray LeCnstr) : GoalM (PArray LeCnstr × Array (Int × LeCnstr)) := do
  let mut cs' := {}
  let mut todo := #[]
  for c in cs do
    let b := c.p.coeff x
    if b == 0 then
      cs' := cs'.push c
    else
      todo := todo.push (b, c)
  return (cs', todo)

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from the inequalities in `todo`.
`todo` contains pairs of the form `(b, c₂)` where `b` is the coefficient of `x` in `c₂`.
-/
private def updateLeCnstrs (a : Int) (x : Var) (c₁ : EqCnstr) (todo : Array (Int × LeCnstr)) : GoalM Unit := do
  for (b, c₂) in todo do
    let c₂ ← c₂.applyEq a x c₁ b
    c₂.assert
    if (← inconsistent) then return ()

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from lower bound inequalities of `y`.
-/
private def updateLowers (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  if (← inconsistent) then return ()
  let (lowers', todo) ← split x (← get').lowers[y]!
  modify' fun s => { s with lowers := s.lowers.set y lowers' }
  updateLeCnstrs a x c todo

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from upper bound inequalities of `y`.
-/
private def updateUppers (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  if (← inconsistent) then return ()
  let (uppers', todo) ← split x (← get').uppers[y]!
  modify' fun s => { s with uppers := s.uppers.set y uppers' }
  updateLeCnstrs a x c todo

private def splitDiseqs (x : Var) (cs : PArray DiseqCnstr) : GoalM (PArray DiseqCnstr × Array (Int × DiseqCnstr)) := do
  let mut cs' := {}
  let mut todo := #[]
  for c in cs do
    let b := c.p.coeff x
    if b == 0 then
      cs' := cs'.push c
    else
      todo := todo.push (b, c)
  return (cs', todo)

private def updateDiseqs (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  if (← inconsistent) then return ()
  let (diseqs', todo) ← splitDiseqs x (← get').diseqs[y]!
  modify' fun s => { s with diseqs := s.diseqs.set y diseqs' }
  for (b, c₂) in todo do
    let c₂ ← c₂.applyEq a x c b
    c₂.assert
    if (← inconsistent) then return ()

private def updateOccsAt (k : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  updateDvdCnstr k x c y
  updateLowers k x c y
  updateUppers k x c y
  updateDiseqs k x c y

private def updateOccs (k : Int) (x : Var) (c : EqCnstr) : GoalM Unit := do
  let ys := (← get').occurs[x]!
  modify' fun s => { s with occurs := s.occurs.set x {} }
  updateOccsAt k x c x
  for y in ys do
    updateOccsAt k x c y

@[export lean_grind_cutsat_assert_eq]
def EqCnstr.assertImpl (c : EqCnstr) : GoalM Unit := do
  if (← inconsistent) then return ()
  trace[grind.cutsat.assert] "{← c.pp}"
  let c ← c.norm.applySubsts
  if c.p.isUnsatEq then
    setInconsistent (.eq c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.eq.trivial] "{← c.pp}"
    return ()
  let k := c.p.gcdCoeffs'
  if c.p.getConst % k > 0 then
    setInconsistent (.eq c)
    return ()
  let c := if k == 1 then
    c
  else
    { p := c.p.div k, h := .divCoeffs c }
  trace[grind.cutsat.eq] "{← c.pp}"
  let some (k, x) := c.p.pickVarToElim? | c.throwUnexpected
  trace[grind.debug.cutsat.subst] ">> {← getVar x}, {← c.pp}"
  modify' fun s => { s with
    elimEqs := s.elimEqs.set x (some c)
    elimStack := x :: s.elimStack
  }
  updateOccs k x c
  if (← inconsistent) then return ()
  -- assert a divisibility constraint IF `|k| != 1`
  if k.natAbs != 1 then
    let p := c.p.insert (-k) x
    let d := Int.ofNat k.natAbs
    { d, p, h := .ofEq x c : DvdCnstr }.assert

private def exprAsPoly (a : Expr) : GoalM Poly := do
  if let some p := (← get').terms.find? { expr := a } then
    return p
  else if let some var := (← get').varMap.find? { expr := a } then
    return .add 1 var (.num 0)
  else if let some k ← getIntValue? a then
    return .num k
  else
    throwError "internal `grind` error, expression is not relevant to cutsat{indentExpr a}"

@[export lean_process_cutsat_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.debug.cutsat.eq] "{a} = {b}"
  let p₁ ← exprAsPoly a
  let p₂ ← exprAsPoly b
  let p := p₁.combine (p₂.mul (-1))
  { p, h := .core p₁ p₂ (← mkEqProof a b) : EqCnstr }.assert

@[export lean_process_cutsat_eq_lit]
def processNewEqLitImpl (a ke : Expr) : GoalM Unit := do
  trace[grind.debug.cutsat.eq] "{a} = {ke}"
  let some k ← getIntValue? ke | return ()
  let p₁ ← exprAsPoly a
  let h ← mkEqProof a ke
  let c ← if k == 0 then
    pure { p := p₁, h := .expr h : EqCnstr }
  else
    let p₂ ← exprAsPoly ke
    let p := p₁.combine (p₂.mul (-1))
    pure { p, h := .core p₁ p₂ h : EqCnstr }
  c.assert

@[export lean_process_cutsat_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.debug.cutsat.diseq] "{a} ≠ {b}"
  let p₁ ← exprAsPoly a
  let some h ← mkDiseqProof? a b
    | throwError "internal `grind` error, failed to build disequality proof for{indentExpr a}\nand{indentExpr b}"
  let c ← if let some 0 ← getIntValue? b then
    pure { p := p₁, h := .expr h : DiseqCnstr }
  else
    let p₂ ← exprAsPoly b
    let p := p₁.combine (p₂.mul (-1))
    pure {p, h := .core p₁ p₂ h : DiseqCnstr }
  c.assert

/-- Different kinds of terms internalized by this module. -/
private inductive SupportedTermKind where
  | add | mul | num

private def isForbiddenParent (parent? : Option Expr) (k : SupportedTermKind) : Bool := Id.run do
  let some parent := parent? | return false
  let .const declName _ := parent.getAppFn | return false
  if declName == ``HAdd.hAdd || declName == ``LE.le || declName == ``Dvd.dvd then return true
  match k with
  | .add => return false
  | .mul => return declName == ``HMul.hMul
  | .num => return declName == ``HMul.hMul || declName == ``Eq

private def internalizeCore (e : Expr) (parent? : Option Expr) (k : SupportedTermKind) : GoalM Unit := do
  if (← get').terms.contains { expr := e } then return ()
  if isForbiddenParent parent? k then return ()
  let p ← toPoly e
  markAsCutsatTerm e
  trace[grind.cutsat.internalize] "{aquote e}:= {← p.pp}"
  modify' fun s => { s with terms := s.terms.insert { expr := e } p }

/--
Internalizes an integer expression. Here are the different cases that are handled.

- `a + b` when `parent?` is not `+`, `≤`, or `∣`
- `k * a` when `k` is a numeral and `parent?` is not `+`, `*`, `≤`, `∣`
- numerals when `parent?` is not `+`, `*`, `≤`, `∣`, `=`.
  Recall that we must internalize numerals to make sure we can propagate equalities
  back to the congruence closure module. Example: we have `f 5`, `f x`, `x - y = 3`, `y = 2`.
-/
def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  let k ← if (← isAdd e) then
    pure .add
  else if (← isMul e) then
    pure .mul
  else if (← getIntValue? e).isSome then
    pure .num
  else
    return ()
  internalizeCore e parent? k

end Lean.Meta.Grind.Arith.Cutsat
