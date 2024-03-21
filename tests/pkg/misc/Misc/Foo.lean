import Lean

open Lean Meta

#eval id (α := MetaM Unit) do
  modifyEnv fun env => env.addExtraName `auxDecl1
  return ()

def foo := 42

local infix:50 " ≺ " => LE.le

#check 1 ≺ 2

local macro "my_refl" : tactic =>
  `(tactic| rfl)

def f (x y : Nat) (_h : x = y := by my_refl) := x

theorem simple : 10 = 10 := by decide
