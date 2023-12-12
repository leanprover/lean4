namespace Ex2
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by _ n =>
  match n with
  | _ => n
end Ex2
