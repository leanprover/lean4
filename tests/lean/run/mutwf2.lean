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

#print isEven
#print isOdd
#print isEven._mutual
