import Lean
import UserAttr.BlaAttr

@[bla] def f (x : Nat) := x + 2
@[bla] def g (x : Nat) := x + 1

@[my_simp] theorem f_eq : f x = x + 2 := rfl
@[my_simp] theorem g_eq : g x = x + 1 := rfl

example : f x + g x = 2*x + 3 := by
  simp_arith -- does not appy f_eq and g_eq
  simp_arith [f, g]

example : f x + g x = 2*x + 3 := by
  simp_arith [my_simp]

example : f x = id (x + 2) := by
  simp
  simp [my_simp]

macro "my_simp" : tactic => `(simp [my_simp])

example : f x = id (x + 2) := by
  my_simp


@[simp low, my_simp low]
theorem expand_mul_add (x y z : Nat) : x * (y + z) = x * y + x * y := sorry
@[simp high, my_simp high]
theorem expand_add_mul (x y z : Nat) : (x + y) * z = x * z + y * z := sorry
@[simp, my_simp]
theorem lassoc_add (x y z : Nat) : x + (y + z) = x + y + z := sorry

set_option trace.Meta.Tactic.simp.rewrite true

-- Rewrites: expand_mul_add -> expand_mul_add -> lassoc_add
theorem ex1 (x : Nat) : (x + x) * (x + x) = x * x + x * x + x * x + x * x := by simp only [my_simp]

-- Rewrites: expand_add_mul -> expand_mul_add -> lassoc_add
theorem ex2 (x : Nat) : (x + x) * (x + x) = x * x + x * x + x * x + x * x := by simp

open Lean
open Lean.Meta
def checkProofs : MetaM Unit := do
  let ConstantInfo.thmInfo info1 ← getConstInfo `ex1 | throwError "unexpected"
  let ConstantInfo.thmInfo info2 ← getConstInfo `ex2 | throwError "unexpected"
  unless info1.value == info2.value do
    throwError "unexpected values"

#eval checkProofs
