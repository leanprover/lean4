/-
Tests for the builtin `@[sym_simp]` attribute.
-/
import Lean

open Lean Elab Tactic Meta

-- Add rewrite theorems to the default set
@[sym_simp] theorem add_zero_nat (a : Nat) : a + 0 = a := Nat.add_zero a
@[sym_simp] theorem zero_add_nat (a : Nat) : 0 + a = a := Nat.zero_add a

-- Add a definition (equation theorems)
@[sym_simp] def myMul : Nat → Nat → Nat
  | 0, _ => 0
  | a + 1, b => b + myMul a b

-- Tactic that uses the default sym_simp set
elab "sym_simp_default" : tactic => do
  let thms ← Sym.Simp.getSymSimpTheorems
  let rewrite := thms.rewrite
  let methods : Sym.Simp.Methods := {
    post := Sym.Simp.evalGround.andThen rewrite
  }
  liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    (← Sym.simpGoal mvarId methods).toOption

-- Test: ground evaluation
example : 2 + 3 = 5 := by sym_simp_default

-- Test: rewrite theorem
example (n : Nat) : n + 0 = n := by sym_simp_default

-- Test: both rewrite theorems
example (n : Nat) : 0 + n + 0 = n := by sym_simp_default

-- Test: equation theorems from definition
example : myMul 3 2 = 6 := by sym_simp_default