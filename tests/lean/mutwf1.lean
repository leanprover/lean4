namespace Ex1
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
termination_by'
  invImage
    (fun
     | Sum.inl ⟨n, true⟩ => (n, 2)
     | Sum.inl ⟨n, false⟩ => (n, 1)
     | Sum.inr n => (n, 0))
  $ Prod.lex sizeOfWFRel sizeOfWFRel
decreasing_by
  simp [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel]
  first
  | apply Prod.Lex.left
    apply Nat.pred_lt
  | apply Prod.Lex.right
    decide
  done -- should fail
end Ex1


namespace Ex2
mutual
  def f : Nat → Bool → Nat
    | n, true  => 2 * f n false
    | 0, false => 1
    | n, false => n + g (n+1) -- Error

  def g (n : Nat) : Nat :=
    if h : n ≠ 0 then
      f (n-1) true
    else
      n
end
termination_by
  f n b => (n, if b then 2 else 1)
  g n   => (n, 0)
end Ex2
