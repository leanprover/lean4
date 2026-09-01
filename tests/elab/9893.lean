import Lean.Elab.Tactic
open Lean Elab Tactic

/-!
# `MVarId.replaceLocalDeclDefEq` should do equality checks after instantiating metavariables
https://github.com/leanprover/lean4/issues/9893
-/

set_option linter.unusedVariables false

elab "test_change_to" t:term "at" h:ident : tactic => withMainContext do
  let e : Expr ← elabTerm t none
  let fvarId ← getFVarId h
  let ty ← fvarId.getType
  logInfo m!"{h} has metavariables: {ty.hasExprMVar}"
  liftMetaTactic1 fun g ↦ do
    let g' ← g.replaceLocalDeclDefEq fvarId e
    logInfo m!"old goal equals new goal: {g == g'}"
    return g'

/-!
This always output 'true'
-/
/--
info: h has metavariables: false
---
info: old goal equals new goal: true
---
trace: x y : Nat
h : x ≤ y
⊢ True
-/
#guard_msgs in
example {x y : Nat} (h : x ≤ y) : True := by
  test_change_to x ≤ y at h
  trace_state
  exact trivial

/-!
This used to output 'false'
-/
/--
info: h has metavariables: true
---
info: old goal equals new goal: true
---
trace: x y : Nat
h : x ≤ y
⊢ True
---
trace: x y : Nat
h : x ≤ y
⊢ True
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example {x y : Nat} : True := by
  have h : ?foo := sorry
  case foo => refine x ≤ ?baz; exact y
  trace_state
  test_change_to x ≤ y at h
  trace_state
  exact trivial

/-!
Make sure the goal changes when the hypothesis changes.
-/
/--
info: h has metavariables: true
---
info: old goal equals new goal: false
---
trace: x y : Nat
h : x ≤ y
⊢ True
---
trace: x y : Nat
h : x ≥ y
⊢ True
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example {x y : Nat} : True := by
  have h : x ≤ y := sorry
  trace_state
  test_change_to x ≥ y at h
  trace_state
  exact trivial
