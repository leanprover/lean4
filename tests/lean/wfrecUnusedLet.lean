def f (n : Nat) : Nat :=
  if h : n = 0 then
    1
  else
    let y := 42
    2 * f (n-1)
decreasing_by
  simp [measure, id, invImage, InvImage, Nat.lt_wfRel, WellFoundedRelation.rel]
  apply Nat.pred_lt h

#print f
