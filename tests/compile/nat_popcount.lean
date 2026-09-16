module
/-! Compiled population count against an independent bit-by-bit reference. -/

def reference (n : Nat) : Nat :=
  (List.range 32).foldl (fun s i => s + (n.testBit i).toNat) 0
public def main : IO Unit := do
  for n in [:65536] do
    unless Nat.popcount n == reference n do throw <| IO.userError s!"popcount mismatch: {n}"
  for k in [63, 64, 65, 127, 128, 247, 248, 249, 255, 256, 495, 496, 497, 4096, 65536] do
    unless (2 ^ k - 1).popcount == k do throw <| IO.userError s!"dense mismatch: {k}"
    unless (2 ^ k).popcount == 1 do throw <| IO.userError s!"sparse mismatch: {k}"
