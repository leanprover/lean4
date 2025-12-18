def Matrix (α β R : Type) := α → β → R

instance [DecidableEq α] : OfNat (Matrix α α Nat) 1 where
  ofNat x y := if x = y then 1 else 0

example [DecidableEq α] (x y : α) (h : x ≠ y) :
    (1 : Matrix α α Nat) x y = 0 := by
  guard_target =ₛ (1 : Matrix ..) x y = 0
  fail_if_success simp
  guard_target =ₛ (1 : Matrix ..) x y = 0
  sorry

example [DecidableEq α] (x y : α) (h : x ≠ y) :
    (1 : Matrix α α Nat) x y = 0 := by
  guard_target =ₛ (1 : Matrix ..) x y = 0
  fail_if_success dsimp
  guard_target =ₛ (1 : Matrix ..) x y = 0
  sorry

theorem one_eq [DecidableEq α] : (1 : Matrix α α Nat) x x = 1 := by
  simp [OfNat.ofNat]

example [DecidableEq α] (x y : α) (h : x ≠ y) :
    (1 : Matrix α α Nat) x y = 0 := by
  guard_target =ₛ (1 : Matrix ..) x y = 0
  simp [OfNat.ofNat, h]
