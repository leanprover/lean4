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
  markAsOffsetTerm expr
  return nodeId

private def getExpr (u : NodeId) : GoalM Expr := do
  return (← get').nodes[u]!

private def getDist? (u v : NodeId) : GoalM (Option Int) := do
  return (← get').targets[u]!.find? v

private def getProof? (u v : NodeId) : GoalM (Option ProofInfo) := do
  return (← get').proofs[u]!.find? v

private def getNodeId (e : Expr) : GoalM NodeId := do
  let some nodeId := (← get').nodeMap.find? { expr := e }
    | throwError "internal `grind` error, term has not been internalized by offset module{indentExpr e}"
  return nodeId

private def getProof (u v : NodeId) : GoalM ProofInfo := do
  let some p ← getProof? u v
    | throwError "internal `grind` error, failed to construct proof for{indentExpr (← getExpr u)}\nand{indentExpr (← getExpr v)}"
  return p

/--
Returns a proof for `u + k ≤ v` (or `u ≤ v + k`) where `k` is the
shortest path between `u` and `v`.
-/
private partial def mkProofForPath (u v : NodeId) : GoalM Expr := do
  go (← getProof u v)
where
  go (p : ProofInfo) : GoalM Expr := do
    if u == p.w then
      return p.proof
    else
      let p' ← getProof u p.w
      go (mkTrans (← get').nodes p' p v)

/--
Given a new edge edge `u --(kuv)--> v` justified by proof `huv` s.t.
it creates a negative cycle with the existing path `v --{kvu}-->* u`, i.e., `kuv + kvu < 0`,
this function closes the current goal by constructing a proof of `False`.
-/
private def setUnsat (u v : NodeId) (kuv : Int) (huv : Expr) (kvu : Int) : GoalM Unit := do
  assert! kuv + kvu < 0
  let hvu ← mkProofForPath v u
  let u ← getExpr u
  let v ← getExpr v
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

/-- Adds `p` to the list of things to be propagated. -/
private def pushToPropagate (p : ToPropagate) : GoalM Unit :=
  modify' fun s => { s with propagate := p :: s.propagate }

private def propagateEqTrue (e : Expr) (u v : NodeId) (k k' : Int) : GoalM Unit := do
  let kuv ← mkProofForPath u v
  let u ← getExpr u
  let v ← getExpr v
  pushEqTrue e <| mkPropagateEqTrueProof u v k kuv k'

private def propagateEqFalse (e : Expr) (u v : NodeId) (k k' : Int) : GoalM Unit := do
  let kuv ← mkProofForPath u v
  let u ← getExpr u
  let v ← getExpr v
  pushEqFalse e <| mkPropagateEqFalseProof u v k kuv k'

/-- Propagates all pending contraints and equalities and resets to "to do" list. -/
private def propagatePending : GoalM Unit := do
  let todo ← modifyGet fun s => (s.arith.offset.propagate, { s with arith.offset.propagate := [] })
  for p in todo do
    match p with
    | .eqTrue e u v k k' => propagateEqTrue e u v k k'
    | .eqFalse e u v k k' => propagateEqFalse e u v k k'
    | .eq u v =>
      let ue ← getExpr u
      let ve ← getExpr v
      unless (← isEqv ue ve) do
        let huv ← mkProofForPath u v
        let hvu ← mkProofForPath v u
        pushEq ue ve <| mkApp4 (mkConst ``Grind.Nat.eq_of_le_of_le) ue ve huv hvu

/--
Given `e` represented by constraint `c` (from `u` to `v`).
Checks whether `e = True` can be propagated using the path `u --(k)--> v`.
If it can, adds a new entry to propagation list.
-/
private def checkEqTrue (u v : NodeId) (k : Int) (c : Cnstr NodeId) (e : Expr) : GoalM Bool := do
  if k ≤ c.k then
    pushToPropagate <| .eqTrue e u v k c.k
    return true
  return false

/--
Given `e` represented by constraint `c` (from `v` to `u`).
Checks whether `e = False` can be propagated using the path `u --(k)--> v`.
If it can, adds a new entry to propagation list.
-/
private def checkEqFalse (u v : NodeId) (k : Int) (c : Cnstr NodeId) (e : Expr) : GoalM Bool := do
  if k + c.k < 0 then
    pushToPropagate <| .eqFalse e u v k c.k
    return true
  return false

/-- Equality propagation. -/
private def checkEq (u v : NodeId) (k : Int) : GoalM Unit := do
  if k != 0 then return ()
  let some k' ← getDist? v u | return ()
  if k' != 0 then return ()
  let ue ← getExpr u
  let ve ← getExpr v
  if (← isEqv ue ve) then return ()
  pushToPropagate <| .eq u v

/--
Auxiliary function for implementing `propagateAll`.
Traverses the constraints `c` (representing an expression `e`) s.t.
`c.u = u` and `c.v = v`, it removes `c` from the list of constraints
associated with `(u, v)` IF
- `e` is already assigned, or
- `f c e` returns true
-/
@[inline]
private def updateCnstrsOf (u v : NodeId) (f : Cnstr NodeId → Expr → GoalM Bool) : GoalM Unit := do
  if let some cs := (← get').cnstrsOf.find? (u, v) then
    let cs' ← cs.filterM fun (c, e) => do
      if (← isEqTrue e <||> isEqFalse e) then
        return false -- constraint was already assigned
      else
        return !(← f c e)
    modify' fun s => { s with cnstrsOf := s.cnstrsOf.insert (u, v) cs' }

/-- Finds constrains and equalities to be propagated. -/
private def checkToPropagate (u v : NodeId) (k : Int) : GoalM Unit := do
  updateCnstrsOf u v fun c e => return !(← checkEqTrue u v k c e)
  updateCnstrsOf v u fun c e => return !(← checkEqFalse u v k c e)
  checkEq u v k

/--
If `isShorter u v k`, updates the shortest distance between `u` and `v`.
`w` is a node in the path from `u` to `v` such that `(← getProof? w v)` is `some`
-/
private def updateIfShorter (u v : NodeId) (k : Int) (w : NodeId) : GoalM Unit := do
  if (← isShorter u v k) then
    setDist u v k
    setProof u v (← getProof w v)
    checkToPropagate u v k

def Cnstr.toExpr (c : Cnstr NodeId) : GoalM Expr := do
  let u := (← get').nodes[c.u]!
  let v := (← get').nodes[c.v]!
  if c.k == 0 then
    return mkNatLE u v
  else if c.k < 0 then
    return mkNatLE (mkNatAdd u (Lean.toExpr ((-c.k).toNat))) v
  else
    return mkNatLE u (mkNatAdd v (Lean.toExpr c.k.toNat))

def checkInvariants : GoalM Unit := do
  let s ← get'
  for u in [:s.targets.size], es in s.targets.toArray do
    for (v, k) in es do
      let c : Cnstr NodeId := { u, v, k }
      trace[grind.debug.offset] "{c}"
      let p ← mkProofForPath u v
      trace[grind.debug.offset.proof] "{p} : {← inferType p}"
      check p
      unless (← withDefault <| isDefEq (← inferType p) (← Cnstr.toExpr c)) do
        trace[grind.debug.offset.proof] "failed: {← inferType p} =?= {← Cnstr.toExpr c}"
        unreachable!

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
    checkToPropagate u v k
    update
    propagatePending
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

private def internalizeCnstr (e : Expr) (c : Cnstr Expr) : GoalM Unit := do
  let u ← mkNode c.u
  let v ← mkNode c.v
  let c := { c with u, v }
  if let some k ← getDist? u v then
    if k ≤ c.k then
      propagateEqTrue e u v k c.k
      return ()
  if let some k ← getDist? v u then
    if k + c.k < 0 then
      propagateEqFalse e v u k c.k
      return ()
  trace[grind.offset.internalize] "{e} ↦ {c}"
  modify' fun s => { s with
    cnstrs   := s.cnstrs.insert { expr := e } c
    cnstrsOf :=
      let cs := if let some cs := s.cnstrsOf.find? (u, v) then (c, e) :: cs else [(c, e)]
      s.cnstrsOf.insert (u, v) cs
  }

private def getZeroNode : GoalM NodeId := do
  mkNode (← getNatZeroExpr)

/-- Internalize `e` of the form `b + k` -/
private def internalizeTerm (e : Expr) (b : Expr) (k : Nat) : GoalM Unit := do
  -- `e` is of the form `b + k`
  let u ← mkNode e
  let v ← mkNode b
  -- `u = v + k`. So, we add edges for `u ≤ v + k` and `v + k ≤ u`.
  let h := mkApp (mkConst ``Nat.le_refl) e
  addEdge u v k h
  addEdge v u (-k) h
  -- `0 + k ≤ u`
  let z ← getZeroNode
  addEdge z u (-k) <| mkApp2 (mkConst ``Grind.Nat.le_offset) b (toExpr k)

/--
Returns `true`, if `parent?` is relevant for internalization.
For example, we do not want to internalize an offset term that
is the child of an addition. This kind of term will be processed by the
more general linear arithmetic module.
-/
private def isRelevantParent (parent? : Option Expr) : GoalM Bool := do
  let some parent := parent? | return false
  let z ← getNatZeroExpr
  return !isNatAdd parent && (isNatOffsetCnstr? parent z).isNone

private def isEqParent (parent? : Option Expr) : Bool := Id.run do
  let some parent := parent? | return false
  return parent.isEq

private def alreadyInternalized (e : Expr) : GoalM Bool := do
  let s ← get'
  return s.cnstrs.contains { expr := e } || s.nodeMap.contains { expr := e }

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  if (← alreadyInternalized e) then
    return ()
  let z ← getNatZeroExpr
  if let some c := isNatOffsetCnstr? e z then
    internalizeCnstr e c
  else if (← isRelevantParent parent?) then
    if let some (b, k) := isNatOffset? e then
      internalizeTerm e b k
    else if let some k := isNatNum? e then
      -- core module has support for detecting equality between literals
      unless isEqParent parent? do
        internalizeTerm e z k

@[export lean_process_new_offset_eq]
def processNewOffsetEqImpl (a b : Expr) : GoalM Unit := do
  unless isSameExpr a b do
    trace[grind.offset.eq.to] "{a}, {b}"
    let u ← getNodeId a
    let v ← getNodeId b
    let h ← mkEqProof a b
    addEdge u v 0 <| mkApp3 (mkConst ``Grind.Nat.le_of_eq_1) a b h
    addEdge v u 0 <| mkApp3 (mkConst ``Grind.Nat.le_of_eq_2) a b h

@[export lean_process_new_offset_eq_lit]
def processNewOffsetEqLitImpl (a b : Expr) : GoalM Unit := do
  unless isSameExpr a b do
    trace[grind.offset.eq.to] "{a}, {b}"
    let some k := isNatNum? b | unreachable!
    let u ← getNodeId a
    let z ← mkNode (← getNatZeroExpr)
    let h ← mkEqProof a b
    addEdge u z k <| mkApp3 (mkConst ``Grind.Nat.le_of_eq_1) a b h
    addEdge z u (-k) <| mkApp3 (mkConst ``Grind.Nat.le_of_eq_2) a b h

def traceDists : GoalM Unit := do
  let s ← get'
  for u in [:s.targets.size], es in s.targets.toArray do
    for (v, k) in es do
      trace[grind.offset.dist] "#{u} -({k})-> #{v}"

end Lean.Meta.Grind.Arith.Offset
