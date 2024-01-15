mutual
  def f : Nat → Bool → Nat
    | n, true  => 2 * f n false
    | 0, false => 1
    | n, false => n + g n
  termination_by n b => (n, if b then 2 else 1)

  def g (n : Nat) : Nat :=
    if h : n ≠ 0 then
      f (n-1) true
    else
      n
  termination_by (n, 0)
end

#print f
#print g
#print f._unary._mutual
