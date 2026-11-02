/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.EPR.Basic
public import Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor
import Lean.Data.UnionFind
import Init.Data.Range.Polymorphic.PRange
import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic.Nat
import Init.Data.Range

/-!
This module implements paradox style sort inference for the EPR problem. While detecting the
potential sorts it also performs a monotonicity analysis. With this information it splits a s
ort up into their subsorts if the parent sort is monotone. This reduces the size of the sorts
and in the process of doing that also the amount of required instances.
-/

namespace Lean.Meta.Tactic.BVDecide.EPR

/-!
Like paradox the algorithm performs a union-find throughout the problem. In the same sweep, it
identifies non-monotone sorts by looking for positive occurences of equality. After all the
information has been collected sorts are split up into their subsorts if their parent is
non-monotone and all sort information relabeled accordingly.
-/

structure InferContext where
  /--
  The EPR problem being processed.
  -/
  eprProblem : EprProblem
  /--
  A map from sort elements to the equivalence class identifier associated with them.
  -/
  elemMap : Std.HashMap Expr Nat := {}
  /--
  A map from predicates to the array of equivalence classes associated with their arguments.
  -/
  predMap : Std.HashMap Expr (Array Nat) := {}

structure InferState where
  /--
  The union find data structure used for sort inference.
  -/
  uf : UnionFind := {}
  /--
  For each equivalence class the sort originally associated with it.
  -/
  classSorts : Array SortId := #[]
  /--
  The set of original sorts that have been identified as non-monotone so far.
  -/
  nonMonotone : Std.HashSet SortId := {}
  /--
  A map from fvars of the quantifier we may currently be under to corresponding equivalence classses.
  -/
  quantMap : Std.HashMap Expr Nat := {}
  /--
  All recorded (quantIdx, quantVarIdx) pairs mapped to their equivalence classes so far.
  -/
  boundClasses : Std.HashMap (Nat × Nat) Nat := {}

abbrev InferM := ReaderT InferContext StateRefT InferState MetaM

@[inline]
def InferM.run (eprProblem : EprProblem) (x : InferM α) : MetaM α :=
  StateRefT'.run' (ReaderT.run x { eprProblem }) {}

def freshClass (sort : SortId) : InferM Nat :=
  modifyGet fun s =>
    let (uf, eqc) := s.uf.push
    (eqc, { s with uf, classSorts := s.classSorts.push sort })

def getRoot (eqc : Nat) : InferM Nat :=
  modifyGet fun s =>
    let (uf, root) := s.uf.find! eqc
    (root, { s with uf })

def getSortClass (e : Expr) : InferM Nat := do
  if let some eqc := (← read).elemMap[e]? then
    return eqc
  else if let some eqc := (← get).quantMap[e]? then
    return eqc
  else
    throwError m!"Term is neither an EPR element nor a quantified variable: {e}"

def unifySortClass (lhs rhs : Nat) : InferM Unit :=
  modify fun s => { s with uf := s.uf.union! lhs rhs }

def markNonMonotone (eqc : Nat) : InferM Unit :=
  modify fun s => { s with nonMonotone := s.nonMonotone.insert s.classSorts[eqc]! }

def isQuantifiedVar (expr : Expr) : InferM Bool :=
  return (← get).quantMap.contains expr

def analyzeFact (e : Expr) : InferM Unit := do
  PolarityVisitor.visitProp e fun e pol => do
    match_expr e with
    | Eq _ lhs rhs =>
      let lhsClass ← getSortClass lhs
      let rhsClass ← getSortClass rhs
      unifySortClass lhsClass rhsClass
      if ← pure pol <&&> (isQuantifiedVar lhs <||> isQuantifiedVar rhs) then
        markNonMonotone lhsClass
    | _ =>
      e.withApp fun pred args => do
        if let some predArgClasses := (← read).predMap[pred]? then
          assert! args.size == predArgClasses.size
          for arg in args, argClass in predArgClasses do
            unifySortClass (← getSortClass arg) argClass

def analyzeQuantifiedFact (fact : QuantifiedFact) (quantIdx : Nat) : InferM Unit :=
  forallBoundedTelescope fact.hyp.type fact.boundSorts.size fun vars body => do
    for h : varIdx in 0...vars.size do
      let eqc ← freshClass fact.boundSorts[varIdx]!
      modify fun s => { s with
        quantMap := s.quantMap.insert vars[varIdx] eqc
        boundClasses := s.boundClasses.insert (quantIdx, varIdx) eqc
      }
    analyzeFact body

structure SortPartition where
  /--
  Map from new sort identifiers to new sort information.
  -/
  sortInfo : Std.HashMap SortId SortInfo := {}
  /--
  The relabeling from old to new sorts if the old sort did not end up getting partitioned.
  We still have to relabel as we use equivalence class identifiers as new sort identifiers and
  old sort ids might clash with equivalence class identifiers.
  -/
  relabeling : Std.HashMap SortId SortId := {}

def partitionSorts : InferM SortPartition := do
  let { eprProblem, elemMap, .. } ← read
  let nonMonotone := (← get).nonMonotone
  let mut partition : SortPartition := {}
  for (sortId, info) in eprProblem.sortInfo do
    let fallback : SortId := ⟨← getRoot elemMap[info.default]!⟩
    partition := { partition with relabeling := partition.relabeling.insert sortId fallback }
    if nonMonotone.contains sortId then
      partition := { partition with sortInfo := partition.sortInfo.insert fallback info }
    else
      for elem in info.elements do
        let newSort : SortId := ⟨← getRoot elemMap[elem]!⟩
        partition := { partition with
          sortInfo := partition.sortInfo.alter newSort fun
            | none => some { info with elements := #[elem] }
            | some info => some { info with elements := info.elements.push elem }
        }
  return partition

def SortPartition.getSort (partition : SortPartition) (eqc : Nat) : InferM SortId := do
  let root : SortId := ⟨← getRoot eqc⟩
  if partition.sortInfo.contains root then
    return root
  else
    return partition.relabeling[(← get).classSorts[eqc]!]!

def analyzeProblem : InferM EprProblem := do
  let { elemMap, predMap, eprProblem := problem } ← read
  problem.groundFacts.forM fun fact => analyzeFact fact.type
  for h : quantIdx in 0...problem.quantifiedFacts.size do
    analyzeQuantifiedFact problem.quantifiedFacts[quantIdx] quantIdx

  let partition ← partitionSorts

  let mut sortMap := {}
  for (elem, eqc) in elemMap do
    sortMap := sortMap.insert elem (← partition.getSort eqc)

  let mut predInfo := {}
  for (pred, info) in problem.predInfo do
    let argumentSorts ← predMap[pred]!.mapM partition.getSort
    predInfo := predInfo.insert pred { info with argumentSorts }

  let quantifiedFacts ← problem.quantifiedFacts.mapIdxM fun quantIdx fact => do
    let boundSorts ← fact.boundSorts.mapIdxM fun varIdx _ => do
      partition.getSort (← get).boundClasses[(quantIdx, varIdx)]!
    return { fact with boundSorts }

  return { problem with sortInfo := partition.sortInfo, sortMap, predInfo, quantifiedFacts }

public def EprProblem.inferSorts (eprProblem : EprProblem) : MetaM EprProblem :=
  InferM.run eprProblem do
    let mut elemMap : Std.HashMap Expr Nat := {}
    for (sortId, info) in eprProblem.sortInfo do
      for element in info.elements do
        elemMap := elemMap.insert element (← freshClass sortId)
    let mut predMap : Std.HashMap Expr (Array Nat) := {}
    for (pred, info) in eprProblem.predInfo do
      predMap := predMap.insert pred (← info.argumentSorts.mapM freshClass)
    withReader (fun ctx => { ctx with elemMap, predMap }) analyzeProblem

end Lean.Meta.Tactic.BVDecide.EPR
