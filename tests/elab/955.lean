namespace Ex2
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  termination_by n =>
    match n with
    | _ => n

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
  termination_by n =>
    match n with
    | _ => n
end
end Ex2
