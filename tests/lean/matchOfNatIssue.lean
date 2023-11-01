example (x : Int) (h : x = 2) : Int.div 2 1 = x := by
  simp [Int.div]
  trace_state
  simp (config := { decide := true }) [h]

example (n : Nat) : Int.div (Int.ofNat n) (Int.ofNat 0) = Int.ofNat (n / 0) := by
  simp [Int.div]

example (n : Nat) : Int.div (Int.ofNat n) 0 = Int.ofNat (n / 0) := by
  simp [Int.div]

example (n : Nat) : Int.mul (Int.ofNat n) (Int.ofNat 0) = Int.ofNat (n * 0) := by
  simp [Int.mul]

example (n : Nat) : Int.mul (Int.ofNat n) 0 = Int.ofNat (n * 0) := by
  simp [Int.mul]
