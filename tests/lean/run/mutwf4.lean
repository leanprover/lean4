set_option trace.Elab.definition.wf true in
mutual
  def f : Nat → Bool → Nat
    | n, true  => 2 * f n false
    | 0, false => 1
    | n, false => n + g n

  def g (n : Nat) : Nat :=
    if h : n ≠ 0 then
      f (n-1) true
    else
      n
end
termination_by
  f n b => (n, if b then 2 else 1)
  g n   => (n, 0)

#print f
#print g
#print f._unary._mutual
