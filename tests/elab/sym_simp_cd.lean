/-
Test for `contextDependent` two-tier cache in Sym.simp.

Uses `dischargeAssumption` (context-dependent) to verify:
- Context-independent results land in persistent cache and survive across invocations.
- Context-dependent results land in transient cache and are re-computed on second invocation.
-/
import Lean

open Lean Elab Tactic Meta

/-- Invoke simp twice on the same goal, threading the persistent cache. -/
elab "sym_simp_twice" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeAssumption
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpControl.andThen Sym.Simp.simpArrowTelescope
    post := Sym.Simp.evalGround.andThen rewrite
  }
  liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    let target := (← mvarId.getDecl).type
    -- First invocation: builds the cache from scratch
    let (_, state) ← Sym.Simp.SimpM.run (Sym.Simp.simp target) methods
    trace[sym.simp.debug.cache] "second traversal"
    -- Second invocation: persistent cache carries over, transient cache is cleared
    let (result, _) ← Sym.Simp.SimpM.run (Sym.Simp.simp target) methods (s := state)
    (← result.toSimpGoalResult mvarId).toOption

-- Test 1: Ground evaluation is context-independent.
-- The second invocation should hit the persistent cache for the whole expression.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: 2 + 3 = 5
-/
#guard_msgs in
example : 2 + 3 = 5 := by
  sym_simp_twice []

-- Test 2: Conditional rewrite using a hypothesis is context-dependent.
-- `dischargeAssumption` uses local hypothesis `h : 0 < n`, so the result is context-dependent
-- and lands in the transient cache. On the second invocation, the transient cache is
-- cleared, so there should be NO persistent cache hit for the overall expression.
-- Only context-independent sub-expressions (literals, fvars) get persistent cache hits.
opaque f : Nat → Nat
axiom f_idem (a : Nat) (_h : 0 < a) : f (f a) = f a

set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] transient cache hit: f (f n)
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] transient cache hit: f (f n)
[sym.simp.debug.cache] persistent cache hit: f n
-/
#guard_msgs in
example (n : Nat) (h : 0 < n) : f (f n) = f (f (f n)) := by
  sym_simp_twice [f_idem]

-- Test 3: Congruence — cd propagates through function application.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n + 7
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: 3 + 4
[sym.simp.debug.cache] persistent cache hit: f n + 7
[sym.simp.debug.cache] persistent cache hit: f n + 7
-/
#guard_msgs in
example (n : Nat) (h : 0 < n) : f (f n) + (3 + 4) = f n + 7 := by
  sym_simp_twice [f_idem]

-- Similar to previous test, but `f_idem` is not applicable (no hypothesis), but discharger must return `cd := true`.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] transient cache hit: f (f n)
[sym.simp.debug.cache] transient cache hit: f (f n) + 7
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: 3 + 4
[sym.simp.debug.cache] transient cache hit: f (f n)
[sym.simp.debug.cache] persistent cache hit: 7
[sym.simp.debug.cache] transient cache hit: f (f n) + 7
-/
#guard_msgs in
example (n : Nat) : f (f n) + (3 + 4) = f (f n) + 7 := by
  sym_simp_twice [f_idem]

-- Test 4: Arrow — cd propagates through implication.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: True
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (n : Nat) (h : 0 < n) : (f (f n) = f n) → True := by
  sym_simp_twice [f_idem]

-- Test 5: Lambda — cd propagates through funext.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: fun x => f n
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: fun x => f n
[sym.simp.debug.cache] persistent cache hit: fun x => f n
-/
#guard_msgs in
example (n : Nat) (_h : 0 < n) : (fun _ : Nat => f (f n)) = (fun _ : Nat => f n) := by
  sym_simp_twice [f_idem]

-- Test 6: Control flow — cd propagates through `ite` condition.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: 1
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: 1
[sym.simp.debug.cache] persistent cache hit: 1
-/
#guard_msgs in
example (n : Nat) (h : 0 < n) : (if f (f n) = f n then 1 else 0) = 1 := by
  sym_simp_twice [f_idem]

-- Test 7: Dependent forall — body cd under binder with `withFreshTransientCache`.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] transient cache hit: f (f n)
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: Nat
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] persistent cache hit: f n
[sym.simp.debug.cache] transient cache hit: f (f n)
[sym.simp.debug.cache] persistent cache hit: f n
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (n : Nat) (h : 0 < n) : ∀ (_ : Nat), f (f n) = f (f (f n)) := by
  sym_simp_twice [f_idem]
