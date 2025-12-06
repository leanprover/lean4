/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
public section
namespace Lean.Meta.Grind.Arith.Cutsat
/-! Collect variable information -/

structure VarInfo where
  maxLowerCoeff : Nat := 0
  maxUpperCoeff : Nat := 0
  maxDvdCoeff   : Nat := 0
  deriving Inhabited

private abbrev CollectM := StateT (Array VarInfo) GoalM

private def updateLower (a : Nat) (x : Var) : CollectM Unit := do
  modify fun infos => infos.modify x fun info => { info with maxLowerCoeff := max a info.maxLowerCoeff }

private def updateUpper (a : Nat) (x : Var) : CollectM Unit := do
  modify fun infos => infos.modify x fun info => { info with maxUpperCoeff := max a info.maxUpperCoeff }

private def updateVarCoeff (a : Int) (x : Var) : CollectM Unit := do
  if a < 0 then updateLower a.natAbs x else updateUpper a.natAbs x

private def updateDvd (a : Nat) (x : Var) : CollectM Unit := do
  modify fun infos => infos.modify x fun info => { info with maxDvdCoeff := max a info.maxDvdCoeff }

private def collectVarInfo : GoalM (Array VarInfo) := do
  let (_, info) ← go |>.run (Array.replicate (← get').vars.size {})
  return info
where
  go : CollectM Unit := do
    let s ← get'
    for x in [: s.vars.size] do
      unless (← eliminated x) do
        for c in s.lowers[x]! do
          visitPoly c.p
        for c in s.uppers[x]! do
          visitPoly c.p
        if let some c := s.dvds[x]! then
          updateDvd c.d.natAbs x

  visitPoly : Poly → CollectM Unit
    | .num .. => return ()
    | .add a x p => do updateVarCoeff a x; visitPoly p

/-!
We order variables in decreasing order of "cost".
We use the lexicographical order of two different costs.
The first one is the `max (min lowerCoeff upperCoeff) dvdCoeff`.
Recall that we use cooper-left if the coefficient of the lower bound is smaller, and cooper-right otherwise.
This is way we use the `min lowerCoeff upperCoeff`. The coefficient of the divisibility constraint also
impacts the size of the search space.
Then, we break ties using the max of all of them, and then the variable original order.
-/
def cost₁ (info : VarInfo) : Nat :=
  max info.maxDvdCoeff (min info.maxLowerCoeff info.maxUpperCoeff)

private def cmp₁ (infos : Array VarInfo) (x y : Var) : Ordering :=
  compare (cost₁ infos[x]!) (cost₁ infos[y]!) |>.swap

def cost₂ (info : VarInfo) : Nat :=
  max info.maxDvdCoeff (max info.maxLowerCoeff info.maxUpperCoeff)

private def cmp₂ (infos : Array VarInfo) (x y : Var) : Ordering :=
  compare (cost₂ infos[x]!) (cost₂ infos[y]!) |>.swap

private def cmp (infos : Array VarInfo) (x y : Var) : Ordering :=
  cmp₁ infos x y |>.then (cmp₂ infos x y) |>.then (compare x y)

private def sortVars : GoalM (Array Var) := do
  let infos ← collectVarInfo
  let result := Array.range (← get').vars.size
  let result := result.qsort (fun x y => cmp infos x y == .lt)
  return result

private def mkPermInv (perm : Array Var) : Array Var := Id.run do
  let mut inv := Array.replicate perm.size 0
  for h : i in [: perm.size] do
    inv := inv.set! perm[i] i
  return inv

def _root_.Int.Linear.Poly.reorder (p : Poly) (old2new : Array Var) : Poly :=
  match p with
  | .num k => .num k
  | .add a x p => .add a old2new[x]! (p.reorder old2new)

def DvdCnstr.reorder (c : DvdCnstr) (old2new : Array Var) : DvdCnstr :=
  { c with p := c.p.reorder old2new, h := .reorder c : DvdCnstr }.norm

def EqCnstr.reorder (c : EqCnstr) (old2new : Array Var) : EqCnstr :=
  { p := c.p.reorder old2new, h := .reorder c : EqCnstr }.norm

def LeCnstr.reorder (c : LeCnstr) (old2new : Array Var) : LeCnstr :=
  { p := c.p.reorder old2new, h := .reorder c : LeCnstr }.norm

def DiseqCnstr.reorder (c : DiseqCnstr) (old2new : Array Var) : DiseqCnstr :=
  { p := c.p.reorder old2new, h := .reorder c : DiseqCnstr }.norm

def reorderVarMap [Inhabited α] (m : PArray α) (new2old : Array Var) : PArray α := Id.run do
  let mut r := {}
  for h : i in [:new2old.size] do
    let j : Nat := new2old[i]
    r := r.push (m.get! j)
  return r

def reorderDiseqSplits (m : PHashMap Poly FVarId) (old2new : Array Var) : PHashMap Poly FVarId := Id.run do
  let mut m' := {}
  for (p, h) in m do
    m' := m'.insert (p.reorder old2new) h
  return m'

def reorderVars : GoalM Unit := do
  let s ← get'
  if s.vars.isEmpty then return () -- nothing to reorder
  /-
  We currently reorder variables at most once.
  It is feasible to implement dynamic variable reordering, but we would have to
  store a trail of vars and varMaps.

  The other option is change our representation and relax the assumption our polynomials are
  sorted. It is unclear how it will impact performance.
  -/
  unless s.vars'.isEmpty do return ()
  checkInvariants
  let new2old ← sortVars
  let old2new := mkPermInv new2old
  -- We save the constraints to reinsert them later.
  let dvds := s.dvds.foldl (init := #[]) fun
    | dvds, none => dvds
    | dvds, some c => dvds.push c
  let dvds := dvds.map (·.reorder old2new)
  let ineqs := s.lowers.foldl (init := #[]) (·.append ·.toArray)
  let ineqs := s.uppers.foldl (init := ineqs) (·.append ·.toArray)
  let ineqs := ineqs.map (·.reorder old2new)
  let diseqs := s.diseqs.foldl (init := #[]) (·.append ·.toArray)
  let diseqs := diseqs.map (·.reorder old2new)
  modify' fun s => { s with
    vars        := reorderVarMap s.vars new2old
    varMap      := s.varMap.map fun x => old2new[x]!
    vars'       := s.vars
    varMap'     := s.varMap
    natDef      := s.natDef.map fun x => old2new[x]!
    dvds        := s.dvds.map fun _ => none
    lowers      := s.lowers.map fun _ => {}
    uppers      := s.uppers.map fun _ => {}
    diseqs      := s.diseqs.map fun _ => {}
    elimEqs     := reorderVarMap s.elimEqs new2old |>.map fun c? => (·.reorder old2new) <$> c?
    elimStack   := s.elimStack.map fun x => old2new[x]!
    occurs      := s.occurs.map fun _ => {}
    diseqSplits := {}
  }
  for c in dvds do c.assert
  for c in ineqs do c.assert
  for c in diseqs do c.assert
  trace[grind.debug.lia.search.reorder] "new2old: {new2old}"
  trace[grind.debug.lia.search.reorder] "old2new: {old2new}"
  checkInvariants

end Lean.Meta.Grind.Arith.Cutsat
