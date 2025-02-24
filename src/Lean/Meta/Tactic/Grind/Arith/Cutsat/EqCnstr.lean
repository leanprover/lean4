/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var

namespace Lean.Meta.Grind.Arith.Cutsat
def mkEqCnstr (p : Poly) (h : EqCnstrProof) : GoalM EqCnstr := do
  return { p, h, id := (← mkCnstrId) }

@[export lean_process_cutsat_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.cutsat.eq] "{mkIntEq a b}"
  -- TODO
  return ()

@[export lean_process_new_cutsat_lit]
def processNewEqLitImpl (a k : Expr) : GoalM Unit := do
  trace[grind.cutsat.eq] "{mkIntEq a k}"
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
