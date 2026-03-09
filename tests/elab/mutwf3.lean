namespace Ex1
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n, a, b => g a n b |>.1
  termination_by n _ _ => (n, 2)
  decreasing_by
    apply Prod.Lex.right
    decide

  def g : α → Nat → α → (α × α)
    | a, 0, b => (a, b)
    | a, n, b => (h a b n, a)
  termination_by _ n _ => (n, 1)
  decreasing_by
    apply Prod.Lex.right
    decide

  def h : α → α → Nat → α
    | _a, b, 0 => b
    | a, b, n+1 => f n a b
  termination_by _ _ n => (n, 0)
  decreasing_by
    apply Prod.Lex.left
    apply Nat.lt_succ_self
end

#guard f 5 'a' 'b' = 'a'

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

#print f._mutual
end Ex1

namespace Ex2
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

#print f._mutual

end Ex2

namespace Ex3
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n, a, b => g a n b |>.1

  def g : α → Nat → α → (α × α)
    | a, 0, b => (a, b)
    | a, n, b => (h a b n, a)

  def h : α → α → Nat → α
    | a, b, 0 => b
    | a, b, n+1 => f n a b
end

#print f._mutual

end Ex3
