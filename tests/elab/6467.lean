theorem confuses_the_user : -(no_index (OfNat.ofNat <| nat_lit 2)) = -2 := by
  simp

theorem ex : -(no_index (OfNat.ofNat <| nat_lit 2)) = (2 : Int) := by
  -- `-2` is already in normal form; the `no_index` annotation does not count as progress.
  fail_if_success simp only [Int.reduceNeg]
  sorry

theorem its_true_really : -(no_index (OfNat.ofNat <| nat_lit 2)) = -2 := by
  rfl

example : -(-(no_index (OfNat.ofNat <| nat_lit 2))) = 2 := by
  simp

example : -(no_index (-(no_index (OfNat.ofNat <| nat_lit 2)))) = -(-(-(-3+1))) := by
  simp
