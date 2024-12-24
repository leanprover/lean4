/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

/-!
Debugging support code for checking basic invariants.
-/

register_builtin_option grind.debug : Bool := {
  defValue := false
  group    := "debug"
  descr    := "check invariants after updates"
}

private def checkEqc (root : ENode) : GoalM Unit := do
  let mut size := 0
  let mut curr := root.self
  repeat
    size := size + 1
    -- The root of `curr` must be `root`
    assert! isSameExpr (← getRoot curr) root.self
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
      -- There is an argument `arg` s.t. root of `arg` is `e`.
      for arg in parent.getAppArgs do
        if isSameExpr (← getRoot arg) e then
          found := true
          break
      assert! found
  else
    -- All the parents are stored in the root of the equivalence class.
    assert! (← getParents e).isEmpty

/--
Check basic invariants if `grind.debug` is enabled.
-/
def checkInvariants : GoalM Unit := do
  if grind.debug.get (← getOptions) then
    for (_, node) in (← get).enodes do
      checkParents node.self
      if isSameExpr node.self node.root then
        checkEqc node

end Lean.Meta.Grind
