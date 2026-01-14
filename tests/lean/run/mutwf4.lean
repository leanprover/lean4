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

/--
info: @[irreducible] def f : Nat → Bool → Nat :=
fun a a_1 => f._mutual (PSum.inl ⟨a, a_1⟩)
-/
#guard_msgs in
#print f

/--
info: @[irreducible] def g : Nat → Nat :=
fun n => f._mutual (PSum.inr n)
-/
#guard_msgs in
#print g

#print f._mutual
