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
  foldEqc root.self (init := #[]) fun n lams =>
    if n.self.isLambda then return lams.push n.self else return lams

/--
Returns the root of the functions in the equivalence class containing `e`.
That is, if `f a` is in `root`s equivalence class, results contains the root of `f`.
-/
def getFnRoots (e : Expr) : GoalM (Array Expr) := do
  foldEqc e (init := #[]) fun n fns => do
    let fn := n.self.getAppFn
    let fnRoot := (← getRoot? fn).getD fn
    if Option.isNone <| fns.find? (isSameExpr · fnRoot) then
      return fns.push fnRoot
    else
      return fns

/--
For each `lam` in `lams` s.t. `lam` and `f` are in the same equivalence class,
propagate `f args = lam args`.
-/
def propagateBetaEqs (lams : Array Expr) (f : Expr) (args : Array Expr) : GoalM Unit := do
  if args.isEmpty then return ()
  for lam in lams do
    let rhs := lam.beta args
    unless rhs.isLambda do
      let mut gen := Nat.max (← getGeneration lam) (← getGeneration f)
      let lhs := mkAppN f args
      if (← hasSameType f lam) then
        let mut h ← mkEqProof f lam
        for arg in args do
          gen := Nat.max gen (← getGeneration arg)
          h ← mkCongrFun h arg
        let eq ← mkEq lhs rhs
        trace[grind.beta] "{eq}, using {lam}"
        addNewFact h eq (gen+1)

/--
Applies beta-reduction for lambdas in `f`s equivalence class.
We use this function while internalizing new applications.
-/
def propagateBetaForNewApp (f : Expr) (args : Array Expr) : GoalM Unit := do
  let some fRoot ← getRoot? f | return ()
  let some n ← getENode? fRoot | return ()
  propagateBetaEqs (← getEqcLambdas n) f args

end Lean.Meta.Grind
