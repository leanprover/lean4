/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Internalize

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
Tries to apply beta-reductiong using the parent applications of the functions in `fns` with
the lambda expressions in `lams`.
-/
def propagateBeta (lams : Array Expr) (fns : Array Expr) : GoalM Unit := do
  if lams.isEmpty then return ()
  let lamRoot ← getRoot lams.back!
  trace[grind.debug.beta] "fns: {fns}, lams: {lams}"
  for fn in fns do
    trace[grind.debug.beta] "fn: {fn}, parents: {(← getParents fn).toArray}"
    for parent in (← getParents fn) do
      let mut args := #[]
      let mut curr := parent
      trace[grind.debug.beta] "parent: {parent}"
      repeat
        trace[grind.debug.beta] "curr: {curr}"
        if (← isEqv curr lamRoot) then
          propagate curr args (Nat.max (← getGeneration curr) (← getGeneration lamRoot))
        let .app f arg := curr
          | break
        -- Remark: recall that we do not eagerly internalize partial applications.
        internalize curr (← getGeneration parent)
        args := args.push arg
        curr := f
where
  propagate (f : Expr) (args : Array Expr) (gen : Nat) : GoalM Unit := do
    if args.isEmpty then return ()
    for lam in lams do
      let lhs := mkAppRev f args
      let rhs := lam.betaRev args
      if (← hasSameType f lam) then
        let mut h ← mkEqProof f lam
        for arg in args.reverse do
          h ← mkCongrFun h arg
        let eq ← mkEq lhs rhs
        trace[grind.beta] "{eq}, using {lam}"
        addNewFact h eq (gen+1)

end Lean.Meta.Grind
