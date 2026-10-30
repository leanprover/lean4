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
  /-- Minimal absolute coefficient over all inequalities containing the variable. -/
  minCoeff      : Nat := 0
  /-- See `State.penalties`. -/
  penalty       : Nat := 0
  deriving Inhabited

private abbrev CollectM := StateT (Array VarInfo) GoalM

private def updateLower (a : Nat) (x : Var) : CollectM Unit := do
  modify fun infos => infos.modify x fun info => { info with maxLowerCoeff := max a info.maxLowerCoeff }

private def updateUpper (a : Nat) (x : Var) : CollectM Unit := do
  modify fun infos => infos.modify x fun info => { info with maxUpperCoeff := max a info.maxUpperCoeff }

private def updateMin (a : Nat) (x : Var) : CollectM Unit := do
  modify fun infos => infos.modify x fun info =>
    { info with minCoeff := if info.minCoeff == 0 then a else min a info.minCoeff }

private def updateVarCoeff (a : Int) (x : Var) : CollectM Unit := do
  updateMin a.natAbs x
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
      if let some penalty := s.penalties.find? { expr := s.vars[x]! } then
        modify fun infos => infos.modify x fun info => { info with penalty }
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
Then, we break ties using the max of all of them.
Remaining ties are broken using the minimal coefficient: a variable that occurs only with large
coefficients (e.g., `t / 64`, which occurs only as `64 * (t / 64)`) produces a Cooper split with
that many cases whenever it is the conflicting variable, while a variable with a unit occurrence
is resolved exactly through that bound. Example: in `t % 64 ≤ (64 * t + y) % 4096 / 64`,
`t`, `(64 * t + y) % 4096 / 64`, and `t / 64` all have `cost₁ = cost₂ = 64`; ordering `t / 64`
first avoids two nested 64-way Cooper splits.
Finally, we use the variable original order.
-/
def cost₁ (info : VarInfo) : Nat :=
  max info.maxDvdCoeff (min info.maxLowerCoeff info.maxUpperCoeff)

private def cmp₁ (infos : Array VarInfo) (x y : Var) : Ordering :=
  compare (cost₁ infos[x]!) (cost₁ infos[y]!) |>.swap

def cost₂ (info : VarInfo) : Nat :=
  max info.maxDvdCoeff (max info.maxLowerCoeff info.maxUpperCoeff)

private def cmp₂ (infos : Array VarInfo) (x y : Var) : Ordering :=
  compare (cost₂ infos[x]!) (cost₂ infos[y]!) |>.swap

private def cmp₃ (infos : Array VarInfo) (x y : Var) : Ordering :=
  compare infos[x]!.minCoeff infos[y]!.minCoeff |>.swap

private def cmpPenalty (infos : Array VarInfo) (x y : Var) : Ordering :=
  compare infos[x]!.penalty infos[y]!.penalty |>.swap

private def cmp (infos : Array VarInfo) (x y : Var) : Ordering :=
  cmpPenalty infos x y |>.then (cmp₁ infos x y) |>.then (cmp₂ infos x y) |>.then (cmp₃ infos x y) |>.then (compare x y)

private def sortVars (infos : Array VarInfo) : GoalM (Array Var) := do
  let result := Array.range (← get').vars.size
  let result := result.qsort (fun x y => cmp infos x y == .lt)
  return result

private def mkPermInv (perm : Array Var) : Array Var := Id.run do
  let mut inv := Array.replicate perm.size 0
  for h : i in [: perm.size] do
    inv := inv.set! perm[i] i
  return inv

def _root_.Int.Internal.Linear.Poly.reorder (p : Poly) (old2new : Array Var) : Poly :=
  match p with
  | .num k => .num k
  | .add a x p => .add a old2new[x]! (p.reorder old2new)

-- Remark: `{ c with ... }` would copy `c.depth?`, see `reorderVars`.
def DvdCnstr.reorder (c : DvdCnstr) (old2new : Array Var) : DvdCnstr :=
  { d := c.d, p := c.p.reorder old2new, h := .reorder c : DvdCnstr }.norm

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

/--
Reorders the variables according to `cmp` when it pays off. Variables created after a
reordering (e.g., by later E-matching rounds) are appended to the order, so an expensive
one may end up after the cheap ones it appears with, and the Cooper case splits that
eliminate it enumerate its coefficient. The first reordering applies the full order; a later
one is performed only when a variable with `cost₁ > 1` is out of place, so that cheap
problems do not accumulate epochs (see `State.varsHistory`). `force := true` reorders whenever
the order changes; it is used after a `requestReorder`.
-/
def reorderVars (force := false) : GoalM Unit := do
  let s ← get'
  if s.vars.isEmpty then return () -- nothing to reorder
  let infos ← collectVarInfo
  let new2old ← sortVars infos
  let old2new := mkPermInv new2old
  let firstTime := s.varsHistory.isEmpty
  let needed := (List.range s.vars.size).any fun x =>
    old2new[x]! != x && (force || firstTime || cost₁ infos[x]! > 1)
  unless needed do return ()
  trace[grind.lia.reorder] "reordering variables, epoch: {s.varsHistory.size + 1}"
  checkInvariants
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
  /-
  The reordered constraints use the new variable order, which does not exist in the goals of the
  enclosing case splits. Thus, they must not inherit the split depth of the original constraints (see
  `markStored`), as they would be hoisted to a goal that uses a different variable order. The `dvds`,
  `ineqs`, and `diseqs` are stored again by `assert`, which records the current depth. The eliminated
  equations are stored directly, so we record the current depth here.
  -/
  let depth ← getGoalStackDepth
  modify' fun s => { s with
    vars        := reorderVarMap s.vars new2old
    varMap      := s.varMap.map fun x => old2new[x]!
    varsHistory := s.varsHistory.push (s.vars, s.varMap)
    natDef      := s.natDef.map fun x => old2new[x]!
    dvds        := s.dvds.map fun _ => none
    lowers      := s.lowers.map fun _ => {}
    uppers      := s.uppers.map fun _ => {}
    diseqs      := s.diseqs.map fun _ => {}
    elimEqs     := reorderVarMap s.elimEqs new2old |>.map fun c? =>
      c?.map fun c => { c.reorder old2new with depth? := some depth }
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
