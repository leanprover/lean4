/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
import Init.Grind.Propagator
import Init.Grind.Order
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Order.Util
import Lean.Meta.Tactic.Grind.Order.Proof
namespace Lean.Meta.Grind.Order
/--
Returns a proof for `u + k ≤ v` (or `u ≤ v + k`) where `k` is the
shortest path between `u` and `v`.
-/
partial def mkProofForPath (u v : NodeId) : OrderM Expr := do
  go (← getProof u v)
where
  go (p : ProofInfo) : OrderM Expr := do
    if u == p.w then
      return p.proof
    else
      let p' ← getProof u p.w
      go (← mkTrans p' p v)

/--
Given a new edge edge `u --(kuv)--> v` justified by proof `huv` s.t.
it creates a negative cycle with the existing path `v --{kvu}-->* u`, i.e., `kuv + kvu < 0`,
this function closes the current goal by constructing a proof of `False`.
-/
def setUnsat (u v : NodeId) (kuv : Weight) (huv : Expr) (kvu : Weight) : OrderM Unit := do
  let hvu ← mkProofForPath v u
  let u ← getExpr u
  let v ← getExpr v
  let h ← mkUnsatProof u v kuv huv kvu hvu
  closeGoal h

/-- Sets the new shortest distance `k` between nodes `u` and `v`. -/
def setDist (u v : NodeId) (k : Weight) : OrderM Unit := do
  modifyStruct fun s => { s with
    targets := s.targets.modify u fun es => es.insert v k
    sources := s.sources.modify v fun es => es.insert u k
  }

def setProof (u v : NodeId) (p : ProofInfo) : OrderM Unit := do
  modifyStruct fun s => { s with
    proofs := s.proofs.modify u fun es => es.insert v p
  }

@[inline] def forEachSourceOf (u : NodeId) (f : NodeId → Weight → OrderM Unit) : OrderM Unit := do
  (← getStruct).sources[u]!.forM f

@[inline] def forEachTargetOf (u : NodeId) (f : NodeId → Weight → OrderM Unit) : OrderM Unit := do
  (← getStruct).targets[u]!.forM f

/-- Returns `true` if `k` is smaller than the shortest distance between `u` and `v` -/
def isShorter (u v : NodeId) (k : Weight) : OrderM Bool := do
  if let some k' ← getDist? u v then
    return k < k'
  else
    return true

/-- Adds `p` to the list of things to be propagated. -/
def pushToPropagate (p : ToPropagate) : OrderM Unit := do
  trace[grind.debug.order.propagate] "{← p.pp}"
  modifyStruct fun s => { s with propagate := p :: s.propagate }

public def propagateEqTrue (c : Cnstr NodeId) (e : Expr) (u v : NodeId) (k k' : Weight) : OrderM Unit := do
  let kuv ← mkProofForPath u v
  let u ← getExpr u
  let v ← getExpr v
  let mut h ← mkPropagateEqTrueProof u v k kuv k'
  if let some he := c.h? then
    h := mkApp4 (mkConst ``Grind.Order.eq_trans_true) e c.e he h
  if let some (e', he) := (← get').cnstrsMapInv.find? { expr := e } then
    h := mkApp4 (mkConst ``Grind.Order.eq_trans_true) e' e he h
    pushEqTrue e' h
  else
    pushEqTrue e h

public def propagateEqFalse (c : Cnstr NodeId) (e : Expr) (u v : NodeId) (k k' : Weight) : OrderM Unit := do
  let kuv ← mkProofForPath u v
  let u ← getExpr u
  let v ← getExpr v
  let mut h ← mkPropagateEqFalseProof u v k kuv k'
  if let some he := c.h? then
    h := mkApp4 (mkConst ``Grind.Order.eq_trans_false) e c.e he h
  if let some (e', he) := (← get').cnstrsMapInv.find? { expr := e } then
    h := mkApp4 (mkConst ``Grind.Order.eq_trans_false) e' e he h
    pushEqFalse e' h
  else
    pushEqFalse e h

/-- Propagates all pending constraints and equalities and resets to "to do" list. -/
def propagatePending : OrderM Unit := do
  let todo := (← getStruct).propagate
  modifyStruct fun s => { s with propagate := [] }
  for p in todo do
    match p with
    | .eqTrue c e u v k k' => propagateEqTrue c e u v k k'
    | .eqFalse c e u v k k' => propagateEqFalse c e u v k k'
    | .eq u v =>
      let ue ← getExpr u
      let ve ← getExpr v
      unless (← isEqv ue ve) do
        let huv ← mkProofForPath u v
        let hvu ← mkProofForPath v u
        let h ← mkEqProofOfLeOfLe ue ve huv hvu
        pushEq ue ve h

/--
Returns `true` if `e` is already `True` in the `grind` core.
Recall that `e` may be an auxiliary term created for a term `e'` (see `cnstrsMapInv`).
-/
private def isAlreadyTrue (e : Expr) : OrderM Bool := do
  if let some (e', _) := (← get').cnstrsMapInv.find? { expr := e } then
    alreadyInternalized e' <&&> isEqTrue e'
  else
    alreadyInternalized e <&&> isEqTrue e

/--
Given `e` represented by constraint `c` (from `u` to `v`).
Checks whether `e = True` can be propagated using the path `u --(k)--> v`.
If it can, adds a new entry to propagation list.
-/
def checkEqTrue (u v : NodeId) (k : Weight) (c : Cnstr NodeId) (e : Expr) : OrderM Bool := do
  if (← isAlreadyTrue e) then return true
  let k' := c.getWeight
  trace[grind.debug.order.check_eq_true] "{← getExpr u}, {← getExpr v}, {k}, {k'}, {← c.pp}"
  if k ≤ k' then
    pushToPropagate <| .eqTrue c e u v k k'
    return true
  else
    return false

/--
Returns `true` if `e` is already `False` in the `grind` core.
Recall that `e` may be an auxiliary term created for a term `e'` (see `cnstrsMapInv`).
-/
private def isAlreadyFalse (e : Expr) : OrderM Bool := do
  if let some (e', _) := (← get').cnstrsMapInv.find? { expr := e } then
    alreadyInternalized e' <&&> isEqFalse e'
  else
    alreadyInternalized e <&&> isEqFalse e

/--
Given `e` represented by constraint `c` (from `v` to `u`).
Checks whether `e = False` can be propagated using the path `u --(k)--> v`.
If it can, adds a new entry to propagation list.
-/
def checkEqFalse (u v : NodeId) (k : Weight) (c : Cnstr NodeId) (e : Expr) : OrderM Bool := do
  if (← isAlreadyFalse e) then return true
  let k' := c.getWeight
  trace[grind.debug.order.check_eq_false] "{← getExpr u}, {← getExpr v}, {k}, {k'} {← c.pp}"
  if (k + k').isNeg  then
    pushToPropagate <| .eqFalse c e u v k k'
    return true
  return false

/--
Auxiliary function for implementing theory propagation.
Traverses the constraints `c` (representing an expression `e`) s.t.
`c.u = u` and `c.v = v`, it removes `c` from the list of constraints
associated with `(u, v)` IF
- `e` is already assigned, or
- `f c e` returns true
-/
@[inline] def updateCnstrsOf (u v : NodeId) (f : Cnstr NodeId → Expr → OrderM Bool) : OrderM Unit := do
  if let some cs := (← getStruct).cnstrsOf.find? (u, v) then
    let cs' ← cs.filterM fun (c, e) => do
      return !(← f c e)
    modifyStruct fun s => { s with cnstrsOf := s.cnstrsOf.insert (u, v) cs' }

/-- Equality propagation. -/
def checkEq (u v : NodeId) (k : Weight) : OrderM Unit := do
  if (← isPartialOrder) then
  if !k.isZero then return ()
  let some k' ← getDist? v u | return ()
  if !k'.isZero then return ()
  let ue ← getExpr u
  let ve ← getExpr v
  if (← alreadyInternalized ue <&&> alreadyInternalized ve) then
    if (← isEqv ue ve) then return ()
    pushToPropagate <| .eq u v

/-- Finds constrains and equalities to be propagated. -/
def checkToPropagate (u v : NodeId) (k : Weight) : OrderM Unit := do
  updateCnstrsOf u v fun c e => checkEqTrue u v k c e
  updateCnstrsOf v u fun c e => checkEqFalse u v k c e
  checkEq u v k

/--
If `isShorter u v k`, updates the shortest distance between `u` and `v`.
`w` is a node in the path from `u` to `v` such that `(← getProof? w v)` is `some`
-/
def updateIfShorter (u v : NodeId) (k : Weight) (w : NodeId) : OrderM Unit := do
  if (← isShorter u v k) then
    setDist u v k
    setProof u v (← getProof w v)
    checkToPropagate u v k

/--
Adds an edge `u --(k) --> v` justified by the proof term `p`, and then
if no negative cycle was created, updates the shortest distance of affected
node pairs.
-/
def addEdge (u : NodeId) (v : NodeId) (k : Weight) (h : Expr) : OrderM Unit := do
  if (← isInconsistent) then return ()
  trace[grind.debug.order.add_edge] "{← getExpr u}, {← getExpr v}, {k}"
  if let some k' ← getDist? v u then
    if (k + k').isNeg then
      setUnsat u v k h k'
      return ()
  if (← isShorter u v k) then
    setDist u v k
    setProof u v { w := u, k, proof := h }
    checkToPropagate u v k
    update
    propagatePending
where
  update : OrderM Unit := do
    forEachTargetOf v fun j k₂ => do
      /- Check whether new path: `u -(k)-> v -(k₂)-> j` is shorter -/
      updateIfShorter u j (k+k₂) v
    forEachSourceOf u fun i k₁ => do
      /- Check whether new path: `i -(k₁)-> u -(k)-> v` is shorter -/
      updateIfShorter i v (k₁+k) u
      forEachTargetOf v fun j k₂ => do
        /- Check whether new path: `i -(k₁)-> u -(k)-> v -(k₂) -> j` is shorter -/
        updateIfShorter i j (k₁+k+k₂) v

/--
Asserts constraint `c` associated with `e` where `he : e = True`.
-/
def assertIneqTrue (c : Cnstr NodeId) (e : Expr) (he : Expr) : OrderM Unit := do
  trace[grind.order.assert] "{← c.pp}"
  let h ←  if let some h := c.h? then
    pure <| mkApp4 (mkConst ``Grind.Order.eq_mp) e c.e h (mkOfEqTrueCore e he)
  else
    pure <| mkOfEqTrueCore e he
  let k : Weight := { k := c.k, strict := c.kind matches .lt }
  addEdge c.u c.v k h

/--
Asserts constraint `c` associated with `e` where `he : e = False`.
-/
def assertIneqFalse (c : Cnstr NodeId) (e : Expr) (he : Expr) : OrderM Unit := do
  unless (← isLinearPreorder) do return ()
  trace[grind.order.assert] "¬ {← c.pp}"
  let h ←  if let some h := c.h? then
    pure <| mkApp4 (mkConst ``Grind.Order.eq_mp_not) e c.e h (mkOfEqFalseCore e he)
  else
    pure <| mkOfEqFalseCore e he
  if (← isRing) then
    let declName := if c.kind matches .lt then
      ``Grind.Order.le_of_not_lt_k
    else
      ``Grind.Order.lt_of_not_le_k
    let h' ← mkLinearOrdRingPrefix declName
    let mut k' := -c.k
    let mut h := mkApp6 h' (← getExpr c.u) (← getExpr c.v) (toExpr c.k) (toExpr k') eagerReflBoolTrue h
    let mut strict := c.kind matches .le
    if (← isInt) && strict then
      h := mkApp6 (mkConst ``Grind.Order.int_lt) (← getExpr c.v) (← getExpr c.u) (toExpr k') (toExpr (k'-1)) eagerReflBoolTrue h
      k'     := k' - 1
      strict := !strict
    addEdge c.v c.u { k := k', strict } h
  else if c.kind matches .lt then
    let h' ← mkLeLtLinearPrefix ``Grind.Order.le_of_not_lt
    let h := mkApp3 h' (← getExpr c.u) (← getExpr c.v) h
    addEdge c.v c.u { strict := false } h
  else if (← hasLt) then
    let h' ← mkLeLtLinearPrefix ``Grind.Order.lt_of_not_le
    let h := mkApp3 h' (← getExpr c.u) (← getExpr c.v) h
    addEdge c.v c.u { strict := true } h
  else
    let h' ← mkLeLinearPrefix ``Grind.Order.le_of_not_le
    let h := mkApp3 h' (← getExpr c.u) (← getExpr c.v) h
    addEdge c.v c.u { strict := false } h

def getStructIdOf? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToStructId.find? { expr := e }

def propagateIneq (e : Expr) : GoalM Unit := do
  if let some (e', he) := (← get').cnstrsMap.find? { expr := e } then
    go e' (some he)
  else
    go e none
where
  go (e' : Expr) (he? : Option Expr) : GoalM Unit := do
    let some structId ← getStructIdOf? e' | return ()
    OrderM.run structId do
    let some c ← getCnstr? e' | return ()
    if (← isEqTrue e) then
      let mut h ← mkEqTrueProof e
      if let some he := he? then
        h := mkApp4 (mkConst ``Grind.Order.eq_trans_true') e e' he h
      assertIneqTrue c e' h
    else if (← isEqFalse e) then
      let mut h ← mkEqFalseProof e
      if let some he := he? then
        h := mkApp4 (mkConst ``Grind.Order.eq_trans_false') e e' he h
      assertIneqFalse c e' h

builtin_grind_propagator propagateLE ↓LE.le := propagateIneq
builtin_grind_propagator propagateLT ↓LT.lt := propagateIneq

public def processNewEq (a b : Expr) : GoalM Unit := do
  unless isSameExpr a b do
    let some id₁ ← getStructIdOf? a | return ()
    let some id₂ ← getStructIdOf? b | return ()
    unless id₁ == id₂ do return ()
    OrderM.run id₁ do
      trace[grind.order.assert] "{a} = {b}"
      let u ← getNodeId a
      let v ← getNodeId b
      let h ← mkEqProof a b
      if (← isRing) then
        let h₁ := mkApp3 (← mkOrdRingPrefix ``Grind.Order.le_of_eq_1_k) a b h
        let h₂ := mkApp3 (← mkOrdRingPrefix ``Grind.Order.le_of_eq_2_k) a b h
        addEdge u v {} h₁
        addEdge v u {} h₂
      else
        let h₁ := mkApp3 (← mkLePreorderPrefix ``Grind.Order.le_of_eq_1) a b h
        let h₂ := mkApp3 (← mkLePreorderPrefix ``Grind.Order.le_of_eq_2) a b h
        addEdge u v {} h₁
        addEdge v u {} h₂

end Lean.Meta.Grind.Order
