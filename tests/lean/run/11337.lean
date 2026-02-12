import Lean

open Lean

structure Foo (n : Nat) where
  (l : List Nat)
  (h : n = n)

def foo (n : Nat) : MetaM Unit := do
  let mut result : Foo n := ⟨[7], rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  result := ⟨List.range n, rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  match n with
  | _ => trace[Meta.Tactic.simp] "{result.l}"

set_option trace.Meta.Tactic.simp true
/--
trace: [Meta.Tactic.simp] [7]
[Meta.Tactic.simp] [0, 1, 2, 3, 4]
[Meta.Tactic.simp] [0, 1, 2, 3, 4]
-/
#guard_msgs in
run_meta do
  foo 5

def bar (n : Nat) : MetaM (List Nat) := do
  let mut result : Foo n := ⟨[7], rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  result := ⟨List.range n, rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  have : Foo n := ⟨[7], rfl⟩
  match n with
  | 0   => pure (); result := ⟨[10], rfl⟩
  | _+1 => result := ⟨[6], rfl⟩
  trace[Meta.Tactic.simp] "{result.l}"
  return result.l

set_option trace.Meta.Tactic.simp true
/--
trace: [Meta.Tactic.simp] [7]
[Meta.Tactic.simp] []
[Meta.Tactic.simp] [10]
[Meta.Tactic.simp] [7]
[Meta.Tactic.simp] [0, 1, 2, 3, 4]
[Meta.Tactic.simp] [6]
-/
#guard_msgs in
run_meta do
  discard <| bar 0
  discard <| bar 5
