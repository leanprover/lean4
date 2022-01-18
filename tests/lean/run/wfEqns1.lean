import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by' measure fun
  | Sum.inl n => n
  | Sum.inr n => n
decreasing_by
  simp [measure, invImage, InvImage, Nat.lt_wfRel]
  apply Nat.lt_succ_self

#print isEven

#eval tst ``isEven
#check @isEven._eq_1
#check @isEven._eq_2
#check @isEven._unfold
