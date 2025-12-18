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

/--
info: @[irreducible] def Ex1.isEven : Nat → Bool :=
fun a => isEven._mutual (PSum.inl a)
-/
#guard_msgs in
#print isEven

/--
info: @[irreducible] def Ex1.isOdd : Nat → Bool :=
fun a => isEven._mutual (PSum.inr a)
-/
#guard_msgs in
#print isOdd

#print isEven._mutual

end Ex1
