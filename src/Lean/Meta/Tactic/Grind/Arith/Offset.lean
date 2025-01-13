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

/--
Returns a proof for `u + k ≤ v` (or `u ≤ v + k`) where `k` is the
shortest path between `u` and `v`.
-/
partial def extractProof (u v : NodeId) : GoalM Expr := do
  go (← getProof? u v).get!
where
  go (p : ProofInfo) : GoalM Expr := do
    if u == p.w then
      return p.proof
    else
      let p' := (← getProof? u p.w).get!
      go (mkTrans (← get').nodes p' p v)

/--
Given a new edge edge `u --(kuv)--> v` justified by proof `huv` s.t.
it creates a negative cycle with the existing path `v --{kvu}-->* u`, i.e., `kuv + kvu < 0`,
this function closes the current goal by constructing a proof of `False`.
-/
private def setUnsat (u v : NodeId) (kuv : Int) (huv : Expr) (kvu : Int) : GoalM Unit := do
  assert! kuv + kvu < 0
  let hvu ← extractProof v u
  let u := (← get').nodes[u]!
  let v := (← get').nodes[v]!
  closeGoal (mkUnsatProof u v kuv huv kvu hvu)

/-- Sets the new shortest distance `k` between nodes `u` and `v`. -/
private def setDist (u v : NodeId) (k : Int) : GoalM Unit := do
  trace[grind.offset.dist] "{({ u, v, k : Cnstr NodeId})}"
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

/-- Returns `true` if `k` is smaller than the shortest distance between `u` and `v` -/
private def isShorter (u v : NodeId) (k : Int) : GoalM Bool := do
  if let some k' ← getDist? u v then
    return k < k'
  else
    return true

/--
If `isShorter u v k`, updates the shortest distance between `u` and `v`.
`w` is the penultimate node in the path from `u` to `v`.
-/
private def updateIfShorter (u v : NodeId) (k : Int) (w : NodeId) : GoalM Unit := do
  if (← isShorter u v k) then
    setDist u v k
    setProof u v (← getProof? w v).get!

/--
Adds an edge `u --(k) --> v` justified by the proof term `p`, and then
if no negative cycle was created, updates the shortest distance of affected
node pairs.
-/
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
  let u := (← get').nodes[c.u]!
  let v := (← get').nodes[c.v]!
  let mk := if c.le then mkNatLE else mkNatEq
  if c.k == 0 then
    return mk u v
  else if c.k < 0 then
    return mk (mkNatAdd u (Lean.toExpr ((-c.k).toNat))) v
  else
    return mk u (mkNatAdd v (Lean.toExpr c.k.toNat))

def checkInvariants : GoalM Unit := do
  let s ← get'
  for u in [:s.targets.size], es in s.targets.toArray do
    for (v, k) in es do
      let c : Cnstr NodeId := { u, v, k }
      trace[grind.debug.offset] "{c}"
      let p ← extractProof u v
      trace[grind.debug.offset.proof] "{p} : {← inferType p}"
      check p
      unless (← withDefault <| isDefEq (← inferType p) (← Cnstr.toExpr c)) do
        trace[grind.debug.offset.proof] "failed: {← inferType p} =?= {← Cnstr.toExpr c}"
        unreachable!

end Lean.Meta.Grind.Arith.Offset
