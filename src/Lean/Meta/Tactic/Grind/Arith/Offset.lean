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
The constraint `x ≤ y + k` is represented as a negative edge.
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

abbrev OffsetM := StateRefT State GoalM

def OffsetM.run (x : OffsetM α) : GoalM α := do
  let os ← modifyGet fun s => (s.arith.offset, { s with arith.offset := {} })
  let (a, os') ← StateRefT'.run x os
  modify fun s => { s with arith.offset := os' }
  return a

def mkNode (expr : Expr) : OffsetM NodeId := do
  if let some nodeId := (← get).nodeMap.find? { expr } then
    return nodeId
  let nodeId : NodeId := (← get).nodes.size
  trace[grind.offset.internalize] "{expr} ↦ #{nodeId}"
  modify fun s => { s with
    nodes   := s.nodes.push expr
    nodeMap := s.nodeMap.insert { expr } nodeId
    sources := s.sources.push {}
    targets := s.targets.push {}
    proofs  := s.proofs.push {}
  }
  return nodeId

def isUnsat : OffsetM Bool :=
  return (← get).unsat.isSome

private def getDist? (u v : NodeId) : OffsetM (Option Int) := do
  return (← get).targets[u]!.find? v

private def getProof? (u v : NodeId) : OffsetM (Option ProofInfo) := do
  return (← get).proofs[u]!.find? v

partial def extractProof (u v : NodeId) : OffsetM Expr := do
  go (← getProof? u v).get!
where
  go (p : ProofInfo) : OffsetM Expr := do
    if u == p.w then
      return p.proof
    else
      let p' := (← getProof? u p.w).get!
      go (mkTrans (← get).nodes p' p v)

private def setUnsat (_u _v : NodeId) (_k : Int) (p : Expr) : OffsetM Unit := do
  modify fun s => { s with
    unsat := p -- TODO
  }

private def setDist (u v : NodeId) (k : Int) : OffsetM Unit := do
  trace[grind.offset] "#{u} -- {k} --> #{v}"
  modify fun s => { s with
    targets := s.targets.modify u fun es => es.insert v k
    sources := s.sources.modify v fun es => es.insert u k
  }

private def setProof (u v : NodeId) (p : ProofInfo) : OffsetM Unit := do
  modify fun s => { s with
    proofs := s.proofs.modify u fun es => es.insert v p
  }

@[inline]
private def forEachSourceOf (u : NodeId) (f : NodeId → Int → OffsetM Unit) : OffsetM Unit := do
  (← get).sources[u]!.forM f

@[inline]
private def forEachTargetOf (u : NodeId) (f : NodeId → Int → OffsetM Unit) : OffsetM Unit := do
  (← get).targets[u]!.forM f

private def isShorter (u v : NodeId) (k : Int) : OffsetM Bool := do
  if let some k' ← getDist? u v then
    return k < k'
  else
    return true

private def updateIfShorter (u v : NodeId) (k : Int) (w : NodeId) : OffsetM Unit := do
  if (← isShorter u v k) then
    setDist u v k
    setProof u v (← getProof? w v).get!

def addEdge (u : NodeId) (v : NodeId) (k : Int) (p : Expr) : OffsetM Unit := do
  if (← isUnsat) then return ()
  if let some k' ← getDist? v u then
    if k'+k < 0 then
      setUnsat u v k p
      return ()
  if (← isShorter u v k) then
    setDist u v k
    setProof u v { w := u, k, proof := p }
    update
where
  update : OffsetM Unit := do
    forEachTargetOf v fun j k₂ => do
      /- Check whether new path: `u -(k)-> v -(k₂)-> j` is shorter -/
      updateIfShorter u j (k+k₂) v
    forEachSourceOf u fun i k₁ => do
      /- Check whether new path: `i -(k₁)-> u -(k)-> v` is shorter -/
      updateIfShorter i v (k₁+k) u
      forEachTargetOf v fun j k₂ => do
        /- Check whether new path: `i -(k₁)-> u -(k)-> v -(k₂) -> j` is shorter -/
        updateIfShorter i j (k₁+k+k₂) v

def traceDists : OffsetM Unit := do
  let s ← get
  for u in [:s.targets.size], es in s.targets.toArray do
    for (v, d) in es do
      trace[grind.offset.dist] "#{u} -({d})-> #{v}"

end Lean.Meta.Grind.Arith.Offset
