set_option pp.coercions false -- Show `OfNat.ofNat` for clarity
set_option pp.natLit true -- Show `nat_lit` for clarity

/--
error: simp made no progress
-/
#guard_msgs (error) in
example (_ : 'a' = x) : 'a' = x := by
  guard_target =ₛ 'a' = x
  simp only

/--
error: simp made no progress
-/
#guard_msgs (error) in
example : 'a' = x := by
-- ⊢ 'a' = x
  simp -- error (as expected): simp made no progress

/--
error: dsimp made no progress
-/
#guard_msgs (error) in
example (_ : 'a' = x) : 'a' = x := by
  guard_target =ₛ 'a' = x
  dsimp only

/--
error: dsimp made no progress
-/
#guard_msgs (error) in
example : 'a' = x := by
-- ⊢ 'a' = x
  dsimp -- error (as expected): simp made no progress
