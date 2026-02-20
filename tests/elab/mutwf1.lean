namespace Ex1
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n, a, b => g a n b |>.1
  termination_by n _ _ => (n, 2)

  def g : α → Nat → α → (α × α)
    | a, 0, b => (a, b)
    | a, n, b => (h a b n, a)
  termination_by _ n _ => (n, 1)

  def h : α → α → Nat → α
    | a, b, 0 => b
    | a, b, n+1 => f n a b
  termination_by _ _ n => (n, 0)
end

/--
info: @[irreducible] def Ex1.f.{u_1} : {α : Type u_1} → Nat → α → α → α :=
fun {α} a a_1 a_2 => f._mutual (PSum.inl ⟨a, ⟨a_1, a_2⟩⟩)
-/
#guard_msgs in
#print f

/--
info: @[irreducible] def Ex1.g.{u_1} : {α : Type u_1} → α → Nat → α → α × α :=
fun {α} a a_1 a_2 => f._mutual (PSum.inr (PSum.inl ⟨a, ⟨a_1, a_2⟩⟩))
-/
#guard_msgs in
#print g

/--
info: @[irreducible] def Ex1.h.{u_1} : {α : Type u_1} → α → α → Nat → α :=
fun {α} a a_1 a_2 => f._mutual (PSum.inr (PSum.inr ⟨a, ⟨a_1, a_2⟩⟩))
-/
#guard_msgs in
#print h

#guard f 5 'a' 'b' == 'a'
end Ex1
