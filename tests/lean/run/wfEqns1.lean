import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  decreasing_by
    sorry

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
  decreasing_by
    sorry
end

#print isEven

#eval tst ``isEven
#check @isEven.eq_1
#check @isEven.eq_2
#check @isEven.def
