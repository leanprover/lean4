/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Offset
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.ProofUtil

namespace Lean.Meta.Grind.Arith.Offset
/-!
This module implements a decision procedure for offset constraints of the form:
```
x + k ≤ y
x ≤ y + k
```
where `k` is a numeral.
Each constraint is represented as an edge in a weighted graph.
The constraint `x + k ≤ y` is represented as a negative edge.
The shortest path between two nodes in the graph corresponds to an implied inequality.
When adding a new edge, the state is considered unsatisfiable if the new edge creates a negative cycle.
An incremental Floyd-Warshall algorithm is used to find the shortest paths between all nodes.
This module can also handle offset equalities of the form `x + k = y` by representing them with two edges:
```
x + k ≤ y
y ≤ x + k
```
The main advantage of this module over a full linear integer arithmetic procedure is
its ability to efficiently detect all implied equalities and inequalities.
-/

def get' : GoalM State := do
  return (← get).arith.offset

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with arith.offset := f s.arith.offset }

def mkNode (expr : Expr) : GoalM NodeId := do
  if let some nodeId := (← get').nodeMap.find? { expr } then
    return nodeId
  let nodeId : NodeId := (← get').nodes.size
  trace[grind.offset.internalize.term] "{expr} ↦ #{nodeId}"
  modify' fun s => { s with
    nodes   := s.nodes.push expr
    nodeMap := s.nodeMap.insert { expr } nodeId
    sources := s.sources.push {}
    targets := s.targets.push {}
    proofs  := s.proofs.push {}
  }
  return nodeId

private def getDist? (u v : NodeId) : GoalM (Option Int) := do
  return (← get').targets[u]!.find? v

private def getProof? (u v : NodeId) : GoalM (Option ProofInfo) := do
  return (← get').proofs[u]!.find? v

partial def extractProof (u v : NodeId) : GoalM Expr := do
  go (← getProof? u v).get!
where
  go (p : ProofInfo) : GoalM Expr := do
    if u == p.w then
      return p.proof
    else
      let p' := (← getProof? u p.w).get!
      go (mkTrans (← get').nodes p' p v)

private def setUnsat (u v : NodeId) (kuv : Int) (huv : Expr) (kvu : Int) : GoalM Unit := do
  assert! kuv + kvu < 0
  let hvu ← extractProof v u
  let u := (← get').nodes[u]!
  let v := (← get').nodes[v]!
  if kuv == 0 then
    assert! kvu < 0
    closeGoal (mkApp6 (mkConst ``Grind.Nat.unsat_le_lo) u v (toExpr (-kvu).toNat) rfl_true huv hvu)
  else if kvu == 0 then
    assert! kuv < 0
    closeGoal (mkApp6 (mkConst ``Grind.Nat.unsat_le_lo) v u (toExpr (-kuv).toNat) rfl_true hvu huv)
  else if kuv < 0 then
    if kvu > 0 then
      closeGoal (mkApp7 (mkConst ``Grind.Nat.unsat_lo_ro) u v (toExpr (-kuv).toNat) (toExpr kvu.toNat) rfl_true huv hvu)
    else
      assert! kvu < 0
      closeGoal (mkApp7 (mkConst ``Grind.Nat.unsat_lo_lo) u v (toExpr (-kuv).toNat) (toExpr (-kvu).toNat) rfl_true huv hvu)
  else
    assert! kuv > 0 && kvu < 0
    closeGoal (mkApp7 (mkConst ``Grind.Nat.unsat_lo_ro) v u (toExpr (-kvu).toNat) (toExpr kuv.toNat) rfl_true hvu huv)

private def setDist (u v : NodeId) (k : Int) : GoalM Unit := do
  trace[grind.offset.dist] "{({ a := u, b := v, k : Cnstr NodeId})}"
  modify' fun s => { s with
    targets := s.targets.modify u fun es => es.insert v k
    sources := s.sources.modify v fun es => es.insert u k
  }

private def setProof (u v : NodeId) (p : ProofInfo) : GoalM Unit := do
  modify' fun s => { s with
    proofs := s.proofs.modify u fun es => es.insert v p
  }

@[inline]
private def forEachSourceOf (u : NodeId) (f : NodeId → Int → GoalM Unit) : GoalM Unit := do
  (← get').sources[u]!.forM f

@[inline]
private def forEachTargetOf (u : NodeId) (f : NodeId → Int → GoalM Unit) : GoalM Unit := do
  (← get').targets[u]!.forM f

private def isShorter (u v : NodeId) (k : Int) : GoalM Bool := do
  if let some k' ← getDist? u v then
    return k < k'
  else
    return true

private def updateIfShorter (u v : NodeId) (k : Int) (w : NodeId) : GoalM Unit := do
  if (← isShorter u v k) then
    setDist u v k
    setProof u v (← getProof? w v).get!

def addEdge (u : NodeId) (v : NodeId) (k : Int) (p : Expr) : GoalM Unit := do
  if (← isInconsistent) then return ()
  if let some k' ← getDist? v u then
    if k'+k < 0 then
      setUnsat u v k p k'
      return ()
  if (← isShorter u v k) then
    setDist u v k
    setProof u v { w := u, k, proof := p }
    update
where
  update : GoalM Unit := do
    forEachTargetOf v fun j k₂ => do
      /- Check whether new path: `u -(k)-> v -(k₂)-> j` is shorter -/
      updateIfShorter u j (k+k₂) v
    forEachSourceOf u fun i k₁ => do
      /- Check whether new path: `i -(k₁)-> u -(k)-> v` is shorter -/
      updateIfShorter i v (k₁+k) u
      forEachTargetOf v fun j k₂ => do
        /- Check whether new path: `i -(k₁)-> u -(k)-> v -(k₂) -> j` is shorter -/
        updateIfShorter i j (k₁+k+k₂) v

def traceDists : GoalM Unit := do
  let s ← get'
  for u in [:s.targets.size], es in s.targets.toArray do
    for (v, k) in es do
      trace[grind.offset.dist] "#{u} -({k})-> #{v}"

def Cnstr.toExpr (c : Cnstr NodeId) : GoalM Expr := do
  let a := (← get').nodes[c.a]!
  let b := (← get').nodes[c.b]!
  let mk := if c.le then mkNatLE else mkNatEq
  if c.k == 0 then
    return mk a b
  else if c.k < 0 then
    return mk (mkNatAdd a (Lean.toExpr ((-c.k).toNat))) b
  else
    return mk a (mkNatAdd b (Lean.toExpr c.k.toNat))

def checkInvariants : GoalM Unit := do
  let s ← get'
  for u in [:s.targets.size], es in s.targets.toArray do
    for (v, k) in es do
      let c : Cnstr NodeId := { a := u, b := v, k }
      trace[grind.debug.offset] "{c}"
      let p ← extractProof u v
      trace[grind.debug.offset.proof] "{p} : {← inferType p}"
      check p
      unless (← withDefault <| isDefEq (← inferType p) (← Cnstr.toExpr c)) do
        trace[grind.debug.offset.proof] "failed: {← inferType p} =?= {← Cnstr.toExpr c}"
        unreachable!

end Lean.Meta.Grind.Arith.Offset
