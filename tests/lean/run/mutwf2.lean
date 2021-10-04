mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by measure fun
  | Sum.inl n => n
  | Sum.inr n => n
decreasing_by
  simp [measure, invImage, InvImage, Nat.lt_wfRel]
  apply Nat.lt_succ_self

#print isEven
#print isOdd
#print isEven._mutual
