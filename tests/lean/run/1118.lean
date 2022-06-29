theorem CongrGood {x y: Nat}: x + y = y + x := by
  conv =>
    congr
    . rw [Nat.add_comm]
    . skip

theorem CongrBad {x y: Nat}: x + y = y + x := by
  have I: True := True.intro;
  conv =>
    congr
    . rw [Nat.add_comm]
    . skip


theorem CongrBad' {x y: Nat}: x + y = y + x := by
  let I: True := True.intro;
  conv =>
    congr
    . rw [Nat.add_comm]
    . skip

theorem CongrBad'' {x y: Nat}: x + y = y + x := by
  let I: True := True.intro;
  try rfl;
  conv =>
    congr
    . rw [Nat.add_comm]
    . skip

theorem CongrGood' {x y: Nat}: x + y = y + x := by
  cases x;
  have I: True := True.intro;
  rw [Nat.add_comm]
  conv =>
    congr
    . rw [Nat.add_comm]
    . skip
