/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr

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

/--
Given a polynomial `p`, returns `some (x, k, c)` if `p` contains the monomial `k*x`,
and `x` has been eliminated using the equality `c`.
-/
def _root_.Int.Linear.Poly.findVarToSubst (p : Poly) : GoalM (Option (Int × Var × EqCnstr)) := do
  match p with
  | .num _ => return none
  | .add k x p =>
    if let some c := (← get').elimEqs[x]! then
      return some (k, x, c)
    else
      findVarToSubst p

partial def applySubsts (c : EqCnstr) : GoalM EqCnstr := do
  let some (a, x, c₁) ← c.p.findVarToSubst | return c
  trace[grind.cutsat.subst] "{← getVar x}, {← c.pp}, {← c₁.pp}"
  let b := c₁.p.coeff x
  let p := c.p.mul (-b) |>.combine (c₁.p.mul a)
  let c ← mkEqCnstr p (.subst x c₁ c)
  applySubsts c

def EqCnstr.assert (c : EqCnstr) : GoalM Unit := do
  if (← isInconsistent) then return ()
  trace[grind.cutsat.assert] "{← c.pp}"
  let c ← c.norm
  let c ← applySubsts c
  -- TODO: check coeffsr
  trace[grind.cutsat.eq] "{← c.pp}"
  let some (k, x) := c.p.pickVarToElim? | c.throwUnexpected
  -- TODO: eliminate `x` from lowers, uppers, and dvdCnstrs
  -- TODO: reset `x`s occurrences
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
  let some p := (← get').terms.find? { expr := a } | return ()
  if k == 0 then
    (← mkEqCnstr p (.expr (← mkEqProof a ke))).assert
  else
    -- TODO
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
