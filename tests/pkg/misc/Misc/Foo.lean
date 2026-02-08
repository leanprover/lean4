import Lean

open Lean Meta

def foo := 42

local infix:50 " ≺ " => LE.le

#check 1 ≺ 2

-- It is possible to bind a local macro to a public auto param but we must opt into it explicitly by
-- separating the `macro_rules` and removing the `local` from it.
local syntax "my_refl" : tactic
macro_rules
  | `(tactic| my_refl) => `(tactic| rfl)

def f (x y : Nat) (_h : x = y := by my_refl) := x

theorem simple : 10 = 10 := by decide
