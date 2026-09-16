module
/-! Compiled population count against an independent bit-by-bit reference. -/

def reference (n : Nat) (width : Nat := 32) : Nat :=
  (List.range width).foldl (fun s i => s + (n.testBit i).toNat) 0
public def main : IO Unit := do
  for n in [:65536] do
    unless Nat.popcount n == reference n do throw <| IO.userError s!"popcount mismatch: {n}"
  for k in [31, 32, 33, 63, 64, 65, 247, 248, 249, 255, 256, 257, 4095, 4096, 4097, 65535, 65536, 65537] do
    unless (2 ^ k - 1).popcount == k do throw <| IO.userError s!"dense mismatch: {k}"
    unless (2 ^ k).popcount == 1 do throw <| IO.userError s!"sparse mismatch: {k}"
  -- Shift a mixed pattern across both 32-bit digits and 64-bit limb boundaries.
  let pattern := 0x5a0f0123456789abcdeff0a581000000015a0f0123456789abcdeff0a58100000001
  for shift in [0, 1, 31, 32, 33, 63, 64, 65, 127, 128, 129, 247, 248, 249, 255, 256, 257, 4095, 4096] do
    let n := (pattern <<< shift) + 0xfedcba9876543210
    unless Nat.popcount n == reference n (shift + 320) do
      throw <| IO.userError s!"mixed-limb mismatch: {shift}"
