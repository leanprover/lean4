/-
Tests for `Sym.simp` theorem set attributes.
-/
module

import SymSimpAttr.Decl
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Sym

open Lean Elab Tactic Meta

-- Add a proposition as a rewrite theorem
@[my_sym_simp] theorem add_zero_nat (a : Nat) : a + 0 = a := Nat.add_zero a

-- Add a definition (equation theorems)
@[my_sym_simp] def myAdd : Nat → Nat → Nat
  | 0, b => b
  | a + 1, b => (myAdd a b) + 1

-- Tactic that uses the theorem set
elab "sym_simp_set" "[" id:ident "]" : tactic => do
  let some ext ← Sym.Simp.getSymSimpExtension? id.getId
    | throwError "Unknown Sym.simp set: {id.getId}"
  let thms ← ext.getTheorems
  let rewrite := thms.rewrite
  let methods : Sym.Simp.Methods := {
    post := Sym.Simp.evalGround.andThen rewrite
  }
  liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    (← Sym.simpGoal mvarId methods).toOption

-- Test: ground evaluation
example : 2 + 3 = 5 := by sym_simp_set [my_sym_simp]

-- Test: rewrite theorem from the set
example (n : Nat) : n + 0 = n := by sym_simp_set [my_sym_simp]

-- Test: equation theorems from definition
example : myAdd 3 2 = 5 := by sym_simp_set [my_sym_simp]
