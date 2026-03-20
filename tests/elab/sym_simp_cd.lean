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
theorem Nat.add_comm_of_pos (a b : Nat) (_h : 0 < a) : a + b = b + a := Nat.add_comm a b

set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
-/
#guard_msgs in
example (n : Nat) (h : 0 < n) : n + 2 = 2 + n := by
  sym_simp_twice [Nat.add_comm_of_pos]

-- Test 3: Congruence — cd propagates through function application.
-- `n + 2` rewrites context-dependently (cd=true), `3 + 4` evaluates ground (cd=false).
-- The congruence combines both, so the overall result is cd=true.
-- On second traversal: ground sub-expressions (`3 + 4`, `7`) hit persistent cache,
-- but cd-tainted expressions (`2 + n`, `2 + n + 7`) are only in transient.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
[sym.simp.debug.cache] transient cache hit: (2 + n) * 7
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 3 + 4
[sym.simp.debug.cache] transient cache hit: 2 + n
[sym.simp.debug.cache] persistent cache hit: 7
[sym.simp.debug.cache] transient cache hit: (2 + n) * 7
-/
#guard_msgs in
example (n : Nat) (h : 0 < n) : (n + 2) * (3 + 4) = (2 + n) * 7 := by
  sym_simp_twice [Nat.add_comm_of_pos]

-- Similar to previous test, but `Nat.add_comm_of_pos` is not applicable, but discharger must return `cd := true`.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] transient cache hit: n + 2
[sym.simp.debug.cache] transient cache hit: (n + 2) * 7
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: 3 + 4
[sym.simp.debug.cache] transient cache hit: n + 2
[sym.simp.debug.cache] persistent cache hit: 7
[sym.simp.debug.cache] transient cache hit: (n + 2) * 7
-/
#guard_msgs in
example (n : Nat) : (n + 2) * (3 + 4) = (n + 2) * 7 := by
  sym_simp_twice [Nat.add_comm_of_pos]

-- Test 4: Arrow — cd propagates through implication.
-- The hypothesis `n + 2 = 2 + n` is simplified context-dependently to `True`.
-- `True → True` simplifies to `True`. The whole result is cd=true.
-- `True` hits persistent cache; `2 + n` is only in transient.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
[sym.simp.debug.cache] persistent cache hit: True
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (n : Nat) (h : 0 < n) : (n + 2 = 2 + n) → True := by
  sym_simp_twice [Nat.add_comm_of_pos]

-- Test 5: Lambda — cd propagates through funext.
-- Body `n + 2` is simplified context-dependently inside the binder.
-- `withFreshTransientCache` clears the transient cache on binder entry.
-- The lambda result `fun x => 2 + n` is only in transient.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: fun x => 2 + n
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: fun x => 2 + n
-/
#guard_msgs in
example (n : Nat) (_h : 0 < n) : (fun _ : Nat => n + 2) = (fun _ : Nat => 2 + n) := by
  sym_simp_twice [Nat.add_comm_of_pos]

-- Test 6: Control flow — cd propagates through `ite` condition.
-- The condition `n + 2 = 2 + n` is simplified context-dependently.
-- The `ite` result inherits cd, and `1` (ground) is in persistent cache.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
[sym.simp.debug.cache] persistent cache hit: 1
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
[sym.simp.debug.cache] persistent cache hit: 1
[sym.simp.debug.cache] persistent cache hit: 1
-/
#guard_msgs in
example (n : Nat) (h : 0 < n) : (if n + 2 = 2 + n then 1 else 0) = 1 := by
  sym_simp_twice [Nat.add_comm_of_pos]

-- Test 7: Dependent forall — body cd under binder with `withFreshTransientCache`.
-- Simplifying `∀ (m : Nat), n + 2 = 2 + n` enters a binder (for `m`).
-- The transient cache is cleared on binder entry (`withFreshTransientCache`).
-- The body uses a cd rewrite, so the overall result is cd=true.
-- After "second traversal": `Nat` (the binder type) hits persistent cache.
set_option trace.sym.simp.debug.cache true in
/--
trace: [sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
[sym.simp.debug.cache] second traversal
[sym.simp.debug.cache] persistent cache hit: Nat
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: 2
[sym.simp.debug.cache] persistent cache hit: n
[sym.simp.debug.cache] transient cache hit: 2 + n
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (n : Nat) (h : 0 < n) : ∀ (_ : Nat), n + 2 = 2 + n := by
  sym_simp_twice [Nat.add_comm_of_pos]
