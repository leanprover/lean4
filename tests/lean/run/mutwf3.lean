namespace Ex1
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n, a, b => g a n b |>.1
  termination_by n _ _ => (n, 2)
  decreasing_by
    simp_wf
    apply Prod.Lex.right
    decide

  def g : α → Nat → α → (α × α)
    | a, 0, b => (a, b)
    | a, n, b => (h a b n, a)
  termination_by _ n _ => (n, 1)
  decreasing_by
    simp_wf
    apply Prod.Lex.right
    decide

  def h : α → α → Nat → α
    | _a, b, 0 => b
    | a, b, n+1 => f n a b
  termination_by _ _ n => (n, 0)
  decreasing_by
    simp_wf
    apply Prod.Lex.left
    apply Nat.lt_succ_self
end

#eval f 5 'a' 'b'
#print f
#print g
#print h
#print f._unary._mutual
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

#print f._unary._mutual

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

#print f._unary._mutual

end Ex3
