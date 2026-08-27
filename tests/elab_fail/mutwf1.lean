namespace Ex1
mutual
  def f : Nat → Bool → Nat
    | n, true  => 2 * f n false
    | 0, false => 1
    | n, false => n + g n
  termination_by n b => (n, if b then 2 else 1)
  decreasing_by
  · apply Prod.Lex.right; decide
  · apply Prod.Lex.right; decide

  def g (n : Nat) : Nat :=
    if h : n ≠ 0 then
      f (n-1) true
    else
      n
  termination_by (n, 0)
  decreasing_by
  apply Prod.Lex.left
  apply Nat.pred_lt
  done -- should fail
end
end Ex1


namespace Ex2
mutual
  def f : Nat → Bool → Nat
    | n, true  => 2 * f n false
    | 0, false => 1
    | n, false => n + g (n+1) -- Error
  termination_by n b => (n, if b then 2 else 1)

  def g (n : Nat) : Nat :=
    if h : n ≠ 0 then
      f (n-1) true
    else
      n
  termination_by (n, 0)
end
end Ex2
