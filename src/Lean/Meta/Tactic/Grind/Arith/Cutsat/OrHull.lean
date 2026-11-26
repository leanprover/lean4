/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Init.Data.Int.OfNat
import Std.Data.TreeMap.Basic
import Std.Data.TreeSet.Basic
import Lean.Meta.Tactic.Grind.Formula
import Lean.Util.MonadCache
import Lean.Meta.NatInstTesters
import Lean.Meta.IntInstTesters
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
public section
namespace Lean.Meta.Grind.Arith.Cutsat
/-!
Hulls of disjunctions.

For each direction `lin`, a formula can imply a bound `lin + k ≤ 0`. Conjunction retains the
strongest bound in that direction. Disjunction takes the weakest bound supported by both sides.
For example, `(b = true ∧ y = x + 1) ∨ (b = false ∧ y = x + 2)` implies `x + 1 ≤ y` and
`y ≤ x + 2`. These bounds compose across successive disjunctions without case splitting.
-/

private structure HullEntry where
  lin : Poly
  k : Int
  atom : OrHullAtom

/-- Positions preserve source order when a conjunction extends either child's table. -/
private structure Bounds where
  ordered : Std.TreeMap Int HullEntry := {}
  index : PHashMap Poly Int := {}
  deriving Inhabited

private def Bounds.insertAt (s : Bounds) (i : Int) (b : HullEntry) : Bounds :=
  { ordered := s.ordered.insert i b, index := s.index.insert b.lin i }

private def Bounds.find? (s : Bounds) (lin : Poly) : Option (Int × HullEntry) := do
  let i ← s.index.find? lin
  return (i, ← s.ordered[i]?)

private def isNatOrInt (α : Expr) : Bool :=
  α.isConstOf ``Nat || α.isConstOf ``Int

private def isArithAtom (e : Expr) : Bool :=
  match_expr e with
  | Eq α _ _ => isNatOrInt α
  | LE.le α _ _ _ => isNatOrInt α
  | _ => false

private structure Atom where
  a : Expr
  b : Expr
  isEq : Bool
  isNat : Bool

private def getAtom? (e : Expr) : MetaM (Option Atom) := do
  match_expr e with
  | Eq α a b =>
    unless isNatOrInt α do return none
    return some ⟨a, b, true, α.isConstOf ``Nat⟩
  | LE.le α inst a b =>
    unless isNatOrInt α do return none
    let isNat := α.isConstOf ``Nat
    unless (← if isNat then Structural.isInstLENat inst else Structural.isInstLEInt inst) do return none
    return some ⟨a, b, false, isNat⟩
  | _ => return none

private def mkEntry (p : Poly) (atom : OrHullAtom) (entries : Bounds) : Bounds :=
  let k := p.getConst
  let lin := p.addConst (-k)
  if lin matches .num _ then entries else entries.insertAt entries.ordered.size { lin, k, atom }

private def atomEntries (gen : Nat) (c : Expr) : GoalM Bounds := do
  let some ⟨a, b, isEq, isNat⟩ ← getAtom? c | return {}
  let (a', b', toIntThm?) ← if isNat then
    let (a', h₁) ← natToInt a
    let (b', h₂) ← natToInt b
    let thm := if isEq then ``Nat.ToInt.of_eq else ``Nat.ToInt.of_le
    pure (a', b', some (mkApp6 (mkConst thm) a b a' b' h₁ h₂))
  else
    pure (a, b, none)
  let lhs ← toLinearExpr a' gen
  let rhs ← toLinearExpr b' gen
  let p := lhs.sub rhs |>.norm
  let atom (kind : OrHullKind) : OrHullAtom := { toIntThm?, lhs, rhs, kind }
  if isEq then
    return mkEntry (p.mul (-1)) (atom .eqNeg) (mkEntry p (atom .eq) {})
  else
    return mkEntry p (atom .le) {}

private def andBounds (as bs : Bounds) : Bounds := Id.run do
  if as.ordered.isEmpty then return bs
  if bs.ordered.isEmpty then return as
  if bs.ordered.size ≤ as.ordered.size then
    return bs.ordered.foldl (init := as) fun s _ b =>
      if let some i := s.index.find? b.lin then
        { s with ordered := s.ordered.modify i fun a => if a.k < b.k then b else a }
      else
        s.insertAt (s.ordered.maxKeyD 0 + 1) b
  -- Prepend the left directions in reverse order, retaining their positions on ties.
  return as.ordered.foldr (init := bs) fun _ a s => Id.run do
    let i := s.ordered.minKeyD 0 - 1
    let some (j, b) := s.find? a.lin | return s.insertAt i a
    return { s with ordered := s.ordered.erase j }.insertAt i (if a.k < b.k then b else a)

private def orBounds (as bs : Bounds) : Bounds := Id.run do
  let leftSmaller := as.ordered.size ≤ bs.ordered.size
  let (xs, ys) := if leftSmaller then (as, bs) else (bs, as)
  let mut result : Bounds := {}
  for (i, x) in xs.ordered do
    let some (j, y) := ys.find? x.lin | continue
    result := result.insertAt (if leftSmaller then i else j) (if x.k ≤ y.k then x else y)
  return result

private structure PreviewState where
  vars : Std.HashMap ExprPtr Var := {}
  directions : Std.HashMap Poly Nat := {}

private abbrev PreviewM := StateRefT PreviewState GoalM

private def previewVar (e : Expr) : PreviewM Var := do
  let e ← shareCommon e
  modifyGet fun s =>
    let next := s.vars.size
    let (prev?, vars) := s.vars.getThenInsertIfNew? { expr := e } next
    (prev?.getD next, { s with vars })

private def previewDirection (lin : Poly) : PreviewM Nat :=
  modifyGet fun s =>
    let next := s.directions.size
    let (prev?, directions) := s.directions.getThenInsertIfNew? lin next
    (prev?.getD next, { s with directions })

private abbrev Directions := Std.TreeSet Nat

private def previewAtom (e : Expr) : PreviewM Directions := do
  let some ⟨a, b, isEq, isNat⟩ ← getAtom? e | return {}
  let (a, b) ← if isNat then
    pure (← shareCommon (← natToIntExpr a), ← shareCommon (← natToIntExpr b))
  else pure (a, b)
  let lhs ← toLinearExprWith previewVar a
  let rhs ← toLinearExprWith previewVar b
  let p := (lhs.sub rhs).norm
  let lin := p.addConst (-p.getConst)
  if lin matches .num _ then return {}
  let dirs := ({} : Directions).insert (← previewDirection lin)
  if isEq then return dirs.insert (← previewDirection (lin.mul (-1)))
  return dirs

/-- A disjunction inside a conjunction contributes only if its alternatives share a direction.
Inspect it before registering any solver terms. All such queries share one direction cache. -/
private def admitConjunct (e : Expr) (supported : Expr → Bool) : MonadCacheT ExprStructEq Directions PreviewM Bool := do
  let_expr Or _ _ := e | return true
  let dirs ← Formula.foldCachedM previewAtom (·.union ·) (·.inter ·) e
    (known? := fun sub => if supported sub then none else some {})
  return !dirs.isEmpty

/-- Asserts the common linear bounds of a disjunction known to be true. -/
def assertOrHull (e : Expr) : GoalM Unit := do
  unless (← getConfig).lia do return ()
  if (← inconsistent) then return ()
  let gen ← getGeneration e
  let fold := Formula.foldRelevantM isArithAtom ({} : Bounds) (·.ordered.isEmpty)
    (fun e => liftM (atomEntries gen e)) andBounds orBounds e (admitConjunct := admitConjunct)
  let summary ← fold.run.run' {}
  if (← inconsistent) then return ()
  for (_, b) in summary.root.ordered do
    let support := fun sub => do
      let (_, a) ← (← summary.find? sub).find? b.lin
      guard (b.k ≤ a.k)
      return a.atom
    let c : LeCnstr := { p := b.lin.addConst b.k, h := .orHull e support }
    c.assert
    if (← inconsistent) then return ()

end Lean.Meta.Grind.Arith.Cutsat
