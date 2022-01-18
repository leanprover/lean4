namespace Ex1
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
termination_by'
  invImage
    (fun
      | Sum.inl ⟨_, n, _, _⟩ => (n, 2)
      | Sum.inr <| Sum.inl ⟨_, _, n, _⟩ => (n, 1)
      | Sum.inr <| Sum.inr ⟨_, _, _, n⟩ => (n, 0))
    (Prod.lex sizeOfWFRel sizeOfWFRel)
decreasing_by
  simp [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel]
  first
  | apply Prod.Lex.left
    apply Nat.lt_succ_self
  | apply Prod.Lex.right
    decide

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

  def g : α → Nat → α → (α × α)
    | a, 0, b => (a, b)
    | a, n, b => (h a b n, a)

  def h : α → α → Nat → α
    | a, b, 0 => b
    | a, b, n+1 => f n a b
end
termination_by'
  invImage
    (fun
      | Sum.inl ⟨_, n, _, _⟩ => (n, 2)
      | Sum.inr <| Sum.inl ⟨_, _, n, _⟩ => (n, 1)
      | Sum.inr <| Sum.inr ⟨_, _, _, n⟩ => (n, 0))
    (Prod.lex sizeOfWFRel sizeOfWFRel)

#print f._unary._mutual

end Ex2
