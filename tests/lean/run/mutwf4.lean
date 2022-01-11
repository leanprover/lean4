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
termination_by'
  invImage
    (fun
     | Sum.inl ⟨n, true⟩ => (n, 2)
     | Sum.inl ⟨n, false⟩ => (n, 1)
     | Sum.inr n => (n, 0))
  $ Prod.lex sizeOfWFRel sizeOfWFRel

#print f
#print g
#print f._unary._mutual
