namespace Ex1
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by' measure fun
  | PSum.inl n => n
  | PSum.inr n => n

#print isEven
#print isOdd
#print isEven._mutual
end Ex1


namespace Ex2
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by _ n => n
end Ex2
