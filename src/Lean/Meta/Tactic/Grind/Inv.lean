/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Proof
import Lean.Meta.Tactic.Grind.Arith.Inv

namespace Lean.Meta.Grind

/-!
Debugging support code for checking basic invariants.
-/

private def checkEqc (root : ENode) : GoalM Unit := do
  let mut size := 0
  let mut curr := root.self
  repeat
    size := size + 1
    -- The root of `curr` must be `root`
    assert! isSameExpr (← getRoot curr) root.self
    -- Check congruence root
    if curr.isApp then
      if let some { e } := (← get).congrTable.find? { e := curr } then
        if (← hasSameType e.getAppFn curr.getAppFn) then
          assert! isSameExpr e (← getCongrRoot curr)
      else
        assert! (← isCongrRoot curr)
    -- If the equivalence class does not have HEq proofs, then the types must be definitionally equal.
    unless root.heqProofs do
      assert! (← hasSameType curr root.self)
    -- Starting at `curr`, following the `target?` field leads to `root`.
    let mut n := curr
    repeat
      if let some target ← getTarget? n then
        n := target
      else
        break
    assert! isSameExpr n root.self
    -- Go to next element
    curr ← getNext curr
    if isSameExpr root.self curr then
      break
  -- The size of the equivalence class is correct.
  assert! root.size == size

private def checkParents (e : Expr) : GoalM Unit := do
  if (← isRoot e) then
    for parent in (← getParents e) do
      let mut found := false
      let checkChild (child : Expr) : GoalM Bool := do
        let some childRoot ← getRoot? child | return false
        return isSameExpr childRoot e
      -- There is an argument `arg` s.t. root of `arg` is `e`.
      for arg in parent.getAppArgs do
        if (← checkChild arg) then
          found := true
          break
      -- Recall that we have support for `Expr.forallE` propagation. See `ForallProp.lean`.
      if let .forallE _ d b _ := parent then
        if (← checkChild d) then
          found := true
        unless b.hasLooseBVars do
          if (← checkChild b) then
            found := true
      unless found do
        assert! (← checkChild parent.getAppFn)
  else
    -- All the parents are stored in the root of the equivalence class.
    assert! (← getParents e).isEmpty

private def checkPtrEqImpliesStructEq : GoalM Unit := do
  let nodes ← getENodes
  for h₁ : i in [: nodes.size] do
    let n₁ := nodes[i]
    for h₂ : j in [i+1 : nodes.size] do
      let n₂ := nodes[j]
      -- We don't have multiple nodes for the same expression
      assert! !isSameExpr n₁.self n₂.self
      -- and the two expressions must not be structurally equal
      assert! !Expr.equal n₁.self n₂.self

private def checkProofs : GoalM Unit := do
  let eqcs ← getEqcs
  for eqc in eqcs do
    for a in eqc do
      for b in eqc do
        unless isSameExpr a b do
          let p ← mkEqHEqProof a b
          trace_goal[grind.debug.proofs] "{a} = {b}"
          check p
          trace_goal[grind.debug.proofs] "checked: {← inferType p}"

/--
Checks basic invariants if `grind.debug` is enabled.
-/
def checkInvariants (expensive := false) : GoalM Unit := do
  if grind.debug.get (← getOptions) then
    for (_, node) in (← get).enodes do
      checkParents node.self
      if isSameExpr node.self node.root then
        checkEqc node
    if expensive then
      checkPtrEqImpliesStructEq
    Arith.checkInvariants
  if expensive && grind.debug.proofs.get (← getOptions) then
    checkProofs

def Goal.checkInvariants (goal : Goal) (expensive := false) : GrindM Unit :=
  discard <| GoalM.run' goal <| Grind.checkInvariants expensive

end Lean.Meta.Grind
