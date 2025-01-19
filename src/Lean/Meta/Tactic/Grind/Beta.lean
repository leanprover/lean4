/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

/-- Returns all lambda expressions in the equivalence class with root `root`. -/
def getEqcLambdas (root : ENode) : GoalM (Array Expr) := do
  unless root.hasLambdas do return #[]
  let mut result := #[]
  let mut curr := root.self
  repeat
    if curr.isLambda then
      result := result.push curr
    let n ← getENode curr
    if isSameExpr n.next root.self then
      return result
    curr := n.next
  return result

/--
Returns the root of the functions in the equivalence class with root `root`.
That is, if `f a` is in `root`s equivalence class, results contains the root of `f`.
-/
def getFnRoots (root : ENode) : GoalM (Array Expr) := do
  let mut result := #[]
  let mut curr := root.self
  repeat
    let fn := curr.getAppFn
    let fnRoot := (← getRoot? fn).getD fn
    if Option.isNone <| result.find? (isSameExpr · fnRoot) then
      result := result.push fnRoot
    let n ← getENode curr
    if isSameExpr n.next root.self then
      return result
    curr := n.next
  return result

/--
Tries to apply beta-reductiong using the parent applications of the functions in `fns` with
the lambda expressions in `lams`.
-/
def propagateBeta (lams : Array Expr) (fns : Array Expr) : GoalM Unit := do
  if lams.isEmpty then do return ()
  trace[grind.debug.beta] "{lams} {fns}"
  -- TODO
  return ()

end Lean.Meta.Grind
