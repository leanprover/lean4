import Lean
open Lean Meta

/-!
Generating equation lemmas adds no `congr_simp` theorems to the environment. A module that
imports such a theorem cannot unfold it, which breaks tools that unfold `congr_simp` theorems
in proofs, such as Mathlib's `to_dual`.
-/

structure S where
  n : Nat
  h : 0 < n + 1

def g (b : Bool) (m : Nat) : S :=
  match b with
  | true => ⟨m + 0, Nat.succ_pos _⟩
  | false => ⟨0, Nat.succ_pos _⟩

/--
info: [g.eq_1, g.eq_2]
---
info: false
-/
#guard_msgs in
run_meta do
  logInfo m!"{(← getEqnsFor? ``g).getD #[]}"
  logInfo m!"{(← getEnv).contains `S.mk.congr_simp}"
