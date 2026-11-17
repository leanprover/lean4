/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.EPR.Basic
import Lean.Data.UnionFind
import Lean.Util.ForEachExprWhere
import Std.Tactic.BVDecide.EPR.BitVec
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic.Nat
import Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor

/-!
This module implements a Z3 style analysis of instantiation sets for the MBQI procedure on
`BitVec` encoded EPR problems. The procedure tracks the following sets:
- For every predicate `p` for each argument position `i` a set of ground terms `A_p_i`
- For every quantified variable `x`
  - a set of ground terms `S_x`, referred to as the instantiation set of `x`
  - a set of variables, called the "avoid set"
  - a set of ground terms, called the "exception set"

In an initial step we analyze all existing quantifiers and visit their propositional atoms with
polarity information:
- `x = t` in:
  - negative polarity: adds the ground term `t` to `S_x`.
  - positive polarity: makes makes `t` an exception for `x` and puts every element of the sort into
    `S_x`.
- `x = y` in:
  - negative polarity: merges all sets of `x` and `y`.
  - positive polarity: puts `x` and `y` into each other's avoid set.
- `p(.., x, ..)` with `x` at position `i` merges the classes of `x` and `A_p_i`.

After this initial analysis of the quantifiers we can inspect the ground instances (and continue to
do so as the CEGAR loop works), here we are interested in correctly maintaining the `A_p_i` sets by
inserting ground terms `t` occuring at position `i` in `p`. In particular, only the positions where
where a variable occurs matter, the rest can be discarded.

By continously updating the instantiation sets during the CEGAR loop we maintain candidate sets of
interesting values for all variables in the form of the `S_x` sets. We use these to limit the search
to interesting instances as opposed to always allowing any member of the sort in.

The avoid and exception sets are used to build clever models of predicates that help this procedure.
-/

namespace Lean.Meta.Tactic.BVDecide.EPR

open Std.Tactic.BVDecide.EPR.BitVec

/--
If `e` is `toBvAux elems h x`, return `x`.
-/
public def toBvAuxArg? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``toBvAux 5 then some e.appArg! else none

/--
If `e` is a full application of `toBvPredₙ`, return `n`. A full application consists of `4 * n`
sort encoding arguments, the predicate itself and `n` `BitVec` arguments.
-/
public def toBvPredAppArity? (e : Expr) : Option Nat :=
  match e.getAppFn with
  | .const name _ =>
    match Option.or toBvPredPropArity[name]? toBvPredBoolArity[name]? with
    | some arity => if e.getAppNumArgs == 5 * arity + 1 then some arity else none
    | none => none
  | _ => none

/--
If `e` is a full application of `toBvPredₙ` return the original predicate and the `BitVec`
arguments it is applied to.
-/
public def toBvPredApp? (e : Expr) : Option (Expr × Array Expr) := do
  let arity ← toBvPredAppArity? e
  let args := e.getAppArgs
  return (args[4 * arity]!, args[(4 * arity + 1)...*].toArray)

/--
The information associated with a frozen class of the instantiation set analysis.
-/
public structure InstClass where
  sort : SortId
  /--
  Whether the instantiation set contains all elements of the sort.
  -/
  full : Bool := false
  /--
  The ground terms in the instantiation set, in the order they were discovered.
  -/
  terms : Array Expr := #[]
  termSet : Std.HashSet Expr := {}
  /--
  Ground terms whose value the projection else value should avoid.
  -/
  exceptions : Std.HashSet Expr := {}
  /--
  Classes whose projection else value the projection else value of this class should avoid.
  -/
  avoid : Std.HashSet Nat := {}
  deriving Inhabited

namespace InstClass

def insertTerm (cls : InstClass) (term : Expr) : InstClass :=
  if cls.termSet.contains term then
    cls
  else
    { cls with terms := cls.terms.push term, termSet := cls.termSet.insert term }

end InstClass

/--
The frozen result of the instantiation set analysis, enriched with ground terms as the CEGAR loop
discovers them.
-/
public structure InstSets where
  /--
  Map from eqc roots to their information.
  -/
  classes : Std.HashMap Nat InstClass := {}
  /--
  For each quantified fact and each of its variables the eqc root of `S_x`.
  -/
  varRoots : Array (Array Nat) := #[]
  /--
  For each `(p, i)` that has a quantified variable at argument `i` of `p` the eqc root of `A_p_i`.
  Exactly these positions require a projection.
  -/
  posRoot : Std.HashMap (Expr × Nat) Nat := {}
  deriving Inhabited

namespace InstSets

structure Builder where
  /--
  The union find used to manage the whole quantifier analysis.
  -/
  uf : UnionFind := {}
  /--
  For each class in `uf` the sort it is associated with.
  -/
  classSorts : Array SortId := #[]
  /--
  Instantiation sets of quantified variables `S_x`.
  -/
  varClasses : Array (Array Nat) := #[]
  /--
  Equivalence classes of application positions `A_p_i`.
  -/
  posClasses : Std.HashMap (Expr × Nat) Nat := {}
  /--
  Ground terms `t` inserted into `S_x`.
  -/
  inserts : Array (Nat × Expr) := #[]
  /--
  The exception set as pairs of `S_x` eqc identifier and terms.
  -/
  exceptions : Array (Nat × Expr) := #[]
  /--
  Avoid relationships between variables.
  -/
  avoids : Array (Nat × Nat) := #[]
  /--
  Used to mark equivalence classes that represent their full sort.
  Tracking them like this is faster than inserting every individual element.
  -/
  full : Array Nat := #[]

abbrev BuildM := StateRefT Builder MetaM

def freshClass (sort : SortId) : BuildM Nat :=
  modifyGet fun s =>
    let (uf, cls) := s.uf.push
    (cls, { s with uf, classSorts := s.classSorts.push sort })

def union (lhs rhs : Nat) : BuildM Unit :=
  modify fun s => { s with uf := s.uf.union! lhs rhs }

def posClass (pred : Expr) (idx : Nat) (sort : SortId) : BuildM Nat := do
  if let some cls := (← get).posClasses[(pred, idx)]? then
    return cls
  let cls ← freshClass sort
  modify fun s => { s with posClasses := s.posClasses.insert (pred, idx) cls }
  return cls

inductive Term where
  | var (cls : Nat)
  | ground (elem : Expr)
  | other

def classify (problem : EprBvProblem) (varMap : Std.HashMap Expr Nat) (e : Expr) : Term :=
  match toBvAuxArg? e with
  | some x =>
    if let some cls := varMap[x]? then
      .var cls
    else if problem.sortMap.contains x then
      .ground x
    else
      .other
  | none => .other

def analyzeAtom (problem : EprBvProblem) (varMap : Std.HashMap Expr Nat) (atom : Expr)
    (pol : Bool) : BuildM Unit := do
  match_expr (meta := false) atom with
  | BEq.beq _ _ lhs rhs =>
    match classify problem varMap lhs, classify problem varMap rhs with
    | .var x, .var y =>
      if pol then
        modify fun s => { s with avoids := s.avoids.push (x, y) |>.push (y, x) }
      else
        union x y
    | .var x, .ground t | .ground t, .var x =>
      if pol then
        modify fun s => { s with exceptions := s.exceptions.push (x, t), full := s.full.push x }
      else
        modify fun s => { s with inserts := s.inserts.push (x, t) }
    | _, _ => return ()
  | _ =>
    let some (pred, args) := toBvPredApp? atom | return ()
    let some info := problem.predInfo[pred]? | return ()
    for h : idx in 0...args.size do
      let .var x := classify problem varMap args[idx] | continue
      union x (← posClass pred idx info.argumentSorts[idx]!)

def analyzeQuantifiedFact (problem : EprBvProblem) (fact : QuantifiedFact) : BuildM Unit := do
  let vars ← fact.boundSorts.mapM freshClass
  modify fun s => { s with varClasses := s.varClasses.push vars }
  forallBoundedTelescope fact.hyp.type fact.boundSorts.size fun xs body => do
  forallBoundedTelescope body fact.boundSorts.size fun _guards body => do
    let_expr Eq _ lhs _ := body | return ()
    let mut varMap := {}
    for x in xs, cls in vars do
      varMap := varMap.insert x cls
    PolarityVisitor.visitBool lhs (analyzeAtom problem varMap)

def freeze : BuildM InstSets := do
  let mut uf := (← get).uf
  let mut roots := Array.emptyWithCapacity uf.size
  for cls in 0...uf.size do
    let (uf', root) := uf.find! cls
    uf := uf'
    roots := roots.push root
  let s ← get
  let mut classes : Std.HashMap Nat InstClass := {}
  for root in roots do
    unless classes.contains root do
      classes := classes.insert root { sort := s.classSorts[root]! }
  for (cls, term) in s.inserts do
    classes := classes.modify roots[cls]! (·.insertTerm term)
  for (cls, term) in s.exceptions do
    classes := classes.modify roots[cls]! fun info => { info with exceptions := info.exceptions.insert term }
  for (cls, other) in s.avoids do
    let (root, otherRoot) := (roots[cls]!, roots[other]!)
    if root == otherRoot then continue
    classes := classes.modify root fun info => { info with avoid := info.avoid.insert otherRoot }
  for cls in s.full do
    classes := classes.modify roots[cls]! ({ · with full := true })
  return {
    classes
    varRoots := s.varClasses.map (·.map (roots[·]!))
    posRoot := s.posClasses.fold (init := {}) fun acc pos cls => acc.insert pos roots[cls]!
  }

/--
Analyze the quantified facts of `problem`. The ground terms of the problem are not taken into
account yet, they have to be added through `addGround`.
-/
public def build (problem : EprBvProblem) : MetaM InstSets := do
  go.run' {}
where
  go : BuildM InstSets := do
    problem.quantifiedFacts.forM (analyzeQuantifiedFact problem)
    freeze

def addGroundApp (sets : InstSets) (app : Expr) : InstSets := Id.run do
  let some (pred, args) := toBvPredApp? app | return sets
  let mut sets := sets
  for h : idx in 0...args.size do
    let some root := sets.posRoot[(pred, idx)]? | continue
    let some elem := toBvAuxArg? args[idx] | continue
    sets := { sets with classes := sets.classes.modify root (·.insertTerm elem) }
  return sets

/--
Add the arguments of all ground predicate applications in `e` to the instantiation sets.
-/
public def addGround (sets : InstSets) (e : Expr) : MetaM InstSets := do
  -- Stopping at `toBvAux` skips the element lists of the sorts and the membership proofs.
  let stop (e : Expr) := e.isAppOf ``toBvAux || (toBvPredAppArity? e).isSome
  let go : StateRefT InstSets MetaM Unit :=
    e.forEachWhere (stopWhenVisited := true) stop fun app =>
      modify (·.addGroundApp app)
  let ((), sets) ← go.run sets
  return sets

def traceClass (root : Nat) (cls : InstClass) : MetaM Unit := do
  let full := if cls.full then ", full" else ""
  let exceptions := cls.exceptions.toArray.qsort Expr.lt
  let avoid := cls.avoid.toArray.qsort (· < ·)
  trace[Meta.Tactic.bv.epr.instSets] m!"class {root}: terms {cls.terms}, exceptions {exceptions}, avoid {avoid}{full}"

public def traceAnalysis (sets : InstSets) : MetaM Unit := do
  unless ← isTracingEnabledFor `Meta.Tactic.bv.epr.instSets do return
  withTraceNode `Meta.Tactic.bv.epr.instSets (fun _ => return m!"Instantiation set analysis") do
    for h : quantIdx in 0...sets.varRoots.size do
      for h : varIdx in 0...sets.varRoots[quantIdx].size do
        trace[Meta.Tactic.bv.epr.instSets] m!"quantifier {quantIdx} variable {varIdx}: class {sets.varRoots[quantIdx][varIdx]}"
    let positions := sets.posRoot.toArray.qsort fun ((p₁, i₁), _) ((p₂, i₂), _) =>
      p₁.lt p₂ || (p₁ == p₂ && i₁ < i₂)
    for ((pred, idx), root) in positions do
      trace[Meta.Tactic.bv.epr.instSets] m!"projection {pred} {idx}: class {root}"
    traceClasses sets
where
  traceClasses (sets : InstSets) : MetaM Unit := do
    for (root, cls) in sets.classes.toArray.qsort (·.1 < ·.1) do
      traceClass root cls

/--
Trace the instantiation sets of all classes that are not unrestricted.
-/
public def traceSets (sets : InstSets) : MetaM Unit := do
  unless ← isTracingEnabledFor `Meta.Tactic.bv.epr.instSets do return
  withTraceNode `Meta.Tactic.bv.epr.instSets (fun _ => return m!"Instantiation sets") do
    for (root, cls) in sets.classes.toArray.qsort (·.1 < ·.1) do
      unless cls.full do
        trace[Meta.Tactic.bv.epr.instSets] m!"class {root}: {cls.terms}"

end InstSets

end Lean.Meta.Tactic.BVDecide.EPR
