example (x : Int) (h : x = 2) : Int.tdiv 2 1 = x := by
  simp [Int.tdiv]
  trace_state
  simp [h]

example (n : Nat) : Int.tdiv (Int.ofNat n) (Int.ofNat 0) = Int.ofNat (n / 0) := by
  simp [Int.tdiv]

example (n : Nat) : Int.tdiv (Int.ofNat n) 0 = Int.ofNat (n / 0) := by
  simp [Int.tdiv]

example (n : Nat) : Int.mul (Int.ofNat n) (Int.ofNat 0) = Int.ofNat (n * 0) := by
  simp [Int.mul]

example (n : Nat) : Int.mul (Int.ofNat n) 0 = Int.ofNat (n * 0) := by
  simp [Int.mul]
