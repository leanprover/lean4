/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Tactic.BVDecide.Normalize.Hyp
import Std.Tactic.BVDecide.EPR.BitVec

/-!
This module defines many-sorted EPR problems and their BitVec encoding.
-/

namespace Lean.Meta.Tactic.BVDecide.EPR

/--
Identifies a sort in a many-sorted EPR problem.
-/
public structure SortId where
  idx : Nat
  deriving Inhabited, Repr, Hashable, DecidableEq

/--
Information about a particular sort in a many-sorted EPR problem.
-/
public structure SortInfo where
  /--
  The Lean level type of the elements in this sort.
  -/
  type : Expr
  /--
  The Level `u` of `type : Type u`.
  -/
  level : Level
  /--
  The elements of the sort as expressions. Every element is expected to have syntactically the same
  Lean type.

  We would usually expect these to be free variables from the goal but this is not guaranteed.
  -/
  elements : Array Expr
  deriving Inhabited

/--
Cardinality of the sort, i.e. the amount of elements it carries.
-/
@[inline]
public def SortInfo.card (info : SortInfo) : Nat := info.elements.size

/--
An expression representing the `Nat` cardinality value of the sort.
-/
@[inline]
public def SortInfo.cardExpr (info : SortInfo) : Expr := toExpr info.card

/--
The default element of the sort.
-/
@[inline]
public def SortInfo.default (info : SortInfo) : Expr := info.elements[0]!

/--
Information about a particular predicate in a many-sorted EPR problem.
-/
public structure PredInfo where
  /--
  For each of the predicate's arguments the sort it belongs to.
  -/
  argumentSorts : Array SortId
  deriving Inhabited

/--
A quantified fact in a many-sorted EPR problem.
-/
public structure QuantifiedFact where
  /--
  The fact itself, we expect that it has `boundSorts.size` leading universal quantifiers, followed
  by an unquantified body.
  -/
  hyp : Normalize.Hyp
  /--
  For each of the leading quantifiers the sort it belongs to.
  -/
  boundSorts : Array SortId
  deriving Inhabited

namespace QuantifiedFact

public def instantiateType (fact : QuantifiedFact) (args : Array Expr) : Expr :=
  fact.hyp.type.getForallBodyMaxDepth fact.boundSorts.size |>.instantiateRev args

public def instantiate (fact : QuantifiedFact) (args : Array Expr) : Sym.SymM Normalize.Hyp := do
  return {
    name := fact.hyp.name ++ `inst
    type := ← Sym.shareCommon <| fact.instantiateType args
    value := mkAppN fact.hyp.value args
    source := fact.hyp.source
  }

end QuantifiedFact

/--
A many-sorted EPR problem.
-/
public structure EprProblem where
  /--
  Information about the sorts participating in the problem.
  -/
  sortInfo : Std.HashMap SortId SortInfo := {}
  /--
  A map from sort element expressions to their associated sort.
  -/
  sortMap : Std.HashMap Expr SortId := {}
  /--
  Information about the predicates participating in the problem.
  -/
  predInfo : Std.HashMap Expr PredInfo := {}
  /--
  The ground facts participating in the problem.
  -/
  groundFacts : Array Normalize.Hyp := {}
  /--
  The quantified facts participating in the problem. Expected to start with some amount of leading
  `∀` followed by a quantifier free body.
  -/
  quantifiedFacts : Array QuantifiedFact := {}
  deriving Inhabited

/--
Information about a BitVec encoded sort in a many-sorted EPR problem.
-/
public structure BvSortInfo extends SortInfo where
  /--
  The chosen width for this sort.
  -/
  width : Nat
  /--
  A function of type `α → BitVec width`.
  -/
  toBv : Expr
  /--
  A function of type `BitVec width → α`.
  -/
  toSort : Expr
  /--
  A reified list of all elements.
  -/
  elemList : Expr
  /--
  A proof that elemList.length < 2^width
  -/
  elemListLt : Expr
  /--
  A map from elements to membership proofs in elemList.
  -/
  elemListMemProofs : Std.HashMap Expr Expr
  deriving Inhabited

/--
The BitVec type associated with the sort described by `info`.
-/
@[inline]
public def BvSortInfo.bvType (info : BvSortInfo) : Expr := toTypeExpr (BitVec info.width)

/--
Apply the sorts BitVec injection to `e`.
-/
@[inline]
public def BvSortInfo.appToBv (info : BvSortInfo) (e : Expr) : Expr := mkApp info.toBv e

public structure BvPredInfo extends PredInfo where
  bvPred : Expr
  eqThm : Expr
  deriving Inhabited

/--
A BitVec encoded many-sorted EPR problem.
-/
public structure EprBvProblem where
  /--
  Information about the sorts participating in the problem as well as their BitVec encoding.
  -/
  sortInfo : Std.HashMap SortId BvSortInfo := {}
  /--
  A map from sort element expressions to their associated sort.
  -/
  sortMap : Std.HashMap Expr SortId := {}
  /--
  Information about the predicates participating in the problem, as well as their BitVec encoding.
  -/
  predInfo : Std.HashMap Expr BvPredInfo := {}
  /--
  The ground facts participating in the problem. All encoded as `BitVec` facts.
  -/
  groundFacts : Array Normalize.Hyp := {}
  /--
  The quantified facts participating in the problem. All encoded as `BitVec` facts.
  -/
  quantifiedFacts : Array QuantifiedFact := {}
  deriving Inhabited

public def toBvPredArity : Std.HashMap Name Nat := {
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁, 1),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₂, 2),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₃, 3),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₄, 4),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₅, 5),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₆, 6),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₇, 7),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₈, 8),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₉, 9),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₀, 10),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₁, 11),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₂, 12),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₃, 13),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₄, 14),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₅, 15),
  (``Std.Tactic.BVDecide.EPR.BitVec.toBvPred₁₆, 16)
}

end Lean.Meta.Tactic.BVDecide.EPR
