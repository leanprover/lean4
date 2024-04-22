namespace Ex1
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  termination_by n => n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
  termination_by n => n
end

#print isEven
#print isOdd
#print isEven._mutual
end Ex1
