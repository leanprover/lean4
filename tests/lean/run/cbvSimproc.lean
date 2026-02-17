import Lean
set_option cbv.warning false

-- Define a pre-simproc (↓) that traces and rewrites `Nat.succ n` to `n + 1`
open Lean Meta Sym.Simp in
cbv_simproc_decl ↓ succToAddPre (Nat.succ _) := fun e => do
  let_expr Nat.succ n := e | return .rfl
  trace[Meta.Tactic.cbv] "pre-simproc fired on: {e}"
  let result ← mkAppM ``HAdd.hAdd #[n, mkNatLit 1]
  let proof ← Sym.mkEqRefl e
  return .step result proof

-- Define a post-simproc (default) that traces and rewrites `List.length []` to `0`
open Lean Meta Sym.Simp in
cbv_simproc_decl lengthNilPost (List.length _) := fun e => do
  let_expr List.length α list := e | return .rfl
  let_expr List.nil _ := list | return .rfl
  trace[Meta.Tactic.cbv] "post-simproc fired on: {e}"
  let result := mkNatLit 0
  let proof ← Sym.mkEqRefl e
  return .step result proof

set_option trace.Meta.Tactic.cbv true

-- Verify the pre-simproc fires and produces a trace message
/--
trace: [Meta.Tactic.cbv] Called cbv tactic to simplify Nat.succ 5
[Meta.Tactic.cbv] pre-simproc fired on: Nat.succ 5
-/
#guard_msgs in
example : Nat.succ 5 = 6 := by
  conv =>
    lhs
    cbv

-- Verify the post-simproc fires and produces a trace message
/--
trace: [Meta.Tactic.cbv] Called cbv tactic to simplify [].length
[Meta.Tactic.cbv] post-simproc fired on: [].length
-/
#guard_msgs in
example : List.length ([] : List Nat) = 0 := by
  conv =>
    lhs
    cbv

-- Test that cbv still works normally without simprocs involved
set_option trace.Meta.Tactic.cbv false
#guard_msgs in
example : 2 + 3 = 5 := by
  conv =>
    lhs
    cbv
