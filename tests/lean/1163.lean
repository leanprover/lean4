import Lean
open Lean Elab Tactic

macro "obviously1" : tactic => `(tactic| exact sorryAx _)

theorem result1 : False := by obviously1

elab "obviously2" : tactic =>
  liftMetaTactic1 fun mvarId => mvarId.admit *> pure none

theorem result2 : False := by obviously2

def x : Bool := 0

theorem result3 : False := by obviously2

theorem result4 : False := by -- Does not generate a `sorry` warning because there is an error
  let x : Bool := 0
  obviously2
