/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Init.Data.Int.OfNat
import Lean.Meta.NatInstTesters
import Lean.Meta.IntInstTesters
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
public section
namespace Lean.Meta.Grind.Arith.Cutsat
/-!
Hulls of disjunctions.

Given a disjunction `d₁ ∨ … ∨ dₙ` that is `True`, where each `dᵢ` is a conjunction containing linear
constraints, we assert the constraints `lin + k ≤ 0` such that every `dᵢ` contains a conjunct
implying `lin + kᵢ ≤ 0` with `k ≤ kᵢ`. For example, `(b = true ∧ y = x + 1) ∨ (b = false ∧ y = x + 2)`
implies `x + 1 ≤ y` and `y ≤ x + 2`.

The hull avoids case splits that only matter for these bounds. For example, after `n` sequential
`if-then-else` statements that add `1` or `2` to `s`, the bound `s₀ + n ≤ sₙ` follows from the hulls
of the `n` disjunctions, while splitting on them produces `2ⁿ` cases.
-/

/-- A constraint `lin + k ≤ 0` implied by a disjunct. The field `alt.k` is set when the hull is known. -/
private structure HullEntry where
  lin : Poly
  k   : Int
  alt : OrHullAlt

private partial def getDisjuncts (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match_expr e with
  | Or a b => getDisjuncts b (acc.push a)
  | _ => acc.push e

private def isNatOrInt (α : Expr) : Bool :=
  α.isConstOf ``Nat || α.isConstOf ``Int

private def isArithAtom (e : Expr) : Bool :=
  match_expr e with
  | Eq α _ _ => isNatOrInt α
  | LE.le α _ _ _ => isNatOrInt α
  | _ => false

/-- Returns the conjuncts of `d` that are linear constraints, and their paths. -/
private partial def getArithConjuncts (d : Expr) (revPath : List Bool := []) (acc : Array (List Bool × Expr) := #[])
    : Array (List Bool × Expr) :=
  match_expr d with
  | And a b => getArithConjuncts b (true :: revPath) (getArithConjuncts a (false :: revPath) acc)
  | _ => if isArithAtom d then acc.push (revPath.reverse, d) else acc

private def mkEntry (p : Poly) (alt : OrHullAlt) (entries : Array HullEntry) : Array HullEntry :=
  let k := p.getConst
  let lin := p.addConst (-k)
  if lin matches .num _ then entries else entries.push { lin, k, alt }

/-- Converts the conjunct `c` at `path` into hull entries. -/
private def pushEntries (gen : Nat) (path : List Bool) (c : Expr) (entries : Array HullEntry) : GoalM (Array HullEntry) := do
  let (a, b, isEq, isNat) ← match_expr c with
    | Eq α a b => pure (a, b, true, α.isConstOf ``Nat)
    | LE.le α inst a b =>
      if α.isConstOf ``Nat then
        unless (← Structural.isInstLENat inst) do return entries
      else
        unless (← Structural.isInstLEInt inst) do return entries
      pure (a, b, false, α.isConstOf ``Nat)
    | _ => return entries
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
  let mkAlt (kind : OrHullKind) : OrHullAlt := { path, toIntThm?, lhs, rhs, kind, k := 0 }
  if isEq then
    return mkEntry (p.mul (-1)) (mkAlt .eqNeg) (mkEntry p (mkAlt .eq) entries)
  else
    return mkEntry p (mkAlt .le) entries

/-- Returns the entry for `lin` with the largest constant, i.e., the strongest one. -/
private def findStrongest? (entries : Array HullEntry) (lin : Poly) : Option HullEntry :=
  entries.foldl (init := none) fun r entry =>
    if entry.lin != lin then r
    else match r with
      | some best => if best.k < entry.k then some entry else r
      | none => some entry

/-- Asserts the hull constraints of the disjunction `e`, which is `True`. -/
def assertOrHull (e : Expr) : GoalM Unit := do
  unless (← getConfig).lia do return ()
  if (← inconsistent) then return ()
  let ds := getDisjuncts e
  let conjss := ds.map (getArithConjuncts ·)
  if conjss.any (·.isEmpty) then return ()
  let gen ← getGeneration e
  let mut entriess : Array (Array HullEntry) := #[]
  for conjs in conjss do
    let mut entries := #[]
    for (path, c) in conjs do
      entries ← pushEntries gen path c entries
    if entries.isEmpty then return ()
    entriess := entriess.push entries
  let some entries₀ := entriess[0]? | return ()
  let mut done : Array Poly := #[]
  for entry in entries₀ do
    if done.contains entry.lin then continue
    done := done.push entry.lin
    let some bests := entriess.mapM (m := Option) (findStrongest? · entry.lin) | continue
    let k := bests.foldl (init := (bests[0]?.map (·.k)).getD entry.k) fun k best => min k best.k
    let alts := bests.map fun best => { best.alt with k := best.k - k }
    let c : LeCnstr := { p := entry.lin.addConst k, h := .orHull e alts }
    c.assert
    if (← inconsistent) then return ()

end Lean.Meta.Grind.Arith.Cutsat
