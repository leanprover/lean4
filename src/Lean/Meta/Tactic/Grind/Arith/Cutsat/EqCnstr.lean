/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr

namespace Lean.Meta.Grind.Arith.Cutsat

def mkEqCnstr (p : Poly) (h : EqCnstrProof) : GoalM EqCnstr := do
  return { p, h, id := (← mkCnstrId) }

def EqCnstr.norm (c : EqCnstr) : GoalM EqCnstr := do
  let c ← if c.p.isSorted then
    pure c
  else
    mkEqCnstr c.p.norm (.norm c)

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
  let some (a, x, c₁) ← c.p.findVarToSubst | return c
  trace[grind.cutsat.subst] "{← getVar x}, {← c.pp}, {← c₁.pp}"
  let b := c₁.p.coeff x
  let p := c.p.mul (-b) |>.combine (c₁.p.mul a)
  let c ← mkEqCnstr p (.subst x c₁ c)
  applySubsts c

private def updateDvdCnstr (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  let some c' := (← get').dvdCnstrs[y]! | return ()
  let b := c'.p.coeff x
  if b == 0 then return ()
  modify' fun s => { s with dvdCnstrs := s.dvdCnstrs.set y none }
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

private def updateOccsAt (k : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  updateDvdCnstr k x c y
  updateLowers k x c y
  updateUppers k x c y

private def updateOccs (k : Int) (x : Var) (c : EqCnstr) : GoalM Unit := do
  let ys := (← get').occurs[x]!
  modify' fun s => { s with occurs := s.occurs.set x {} }
  updateOccsAt k x c x
  for y in ys do
    updateOccsAt k x c y

def EqCnstr.assert (c : EqCnstr) : GoalM Unit := do
  if (← inconsistent) then return ()
  trace[grind.cutsat.assert] "{← c.pp}"
  let c ← c.norm
  let c ← c.applySubsts
  if c.p.isUnsatEq then
    setInconsistent (.eq c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.le.trivial] "{← c.pp}"
    return ()
  let k := c.p.gcdCoeffs'
  if c.p.getConst % k > 0 then
    setInconsistent (.eq c)
    return ()
  let c ← if k == 1 then
    pure c
  else
    mkEqCnstr (c.p.div k) (.divCoeffs c)
  trace[grind.cutsat.eq] "{← c.pp}"
  let some (k, x) := c.p.pickVarToElim? | c.throwUnexpected
  updateOccs k x c
  if (← inconsistent) then return ()
  -- assert a divisibility constraint IF `|k| != 1`
  if k.natAbs != 1 then
    let p := c.p.insert (-k) x
    let d := Int.ofNat k.natAbs
    let c ← mkDvdCnstr d p (.ofEq x c)
    c.assert
  modify' fun s => { s with
    elimEqs := s.elimEqs.set x (some c)
    elimStack := x :: s.elimStack
  }

@[export lean_process_cutsat_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.cutsat.eq] "{mkIntEq a b}"
  -- TODO
  return ()

@[export lean_process_new_cutsat_lit]
def processNewEqLitImpl (a ke : Expr) : GoalM Unit := do
  let some k ← getIntValue? ke | return ()
  if let some p := (← get').terms.find? { expr := a } then
    if k == 0 then
      (← mkEqCnstr p (.expr (← mkEqProof a ke))).assert
    else
      -- TODO
      return ()
  else
    -- TODO: `a` is a variable
    return ()

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
