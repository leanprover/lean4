/-- info: [true, true, false, true, false, false, true, true, false, true, false, false] -/
#guard_msgs in
#eval [Nat.ble 36 37, Nat.ble 37 37, Nat.ble 38 37, Nat.blt 36 37, Nat.blt 37 37, Nat.blt 38 37, 36 ≤ 37, 37 ≤ 37, 38 ≤ 37 ,36 < 37, 37 < 37, 38 < 37]
