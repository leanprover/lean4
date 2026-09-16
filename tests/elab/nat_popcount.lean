module
import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
/-! Native and kernel population count, including multi-limb results and BitVec clients. -/
example : Nat.popcount 0 = 0 := by decide +kernel
example : Nat.popcount 255 = 8 := by decide +kernel
example : Nat.popcount (2 ^ 256 - 1) = 256 := by decide +kernel
example : Nat.popcount (2 ^ 4096 + 2 ^ 64 + 1) = 3 := by decide +kernel
example : (0#0).cpop = 0#0 := by decide +kernel
example : (1#65536).cpop = 1#65536 := by decide +kernel
example : (511#9).cpop = 9#9 := by decide +kernel
example (x : BitVec 8) : x.cpop ≤ 8#8 := by bv_decide

def reference (n : Nat) : Nat :=
  (List.range 32).foldl (fun s i => s + (n.testBit i).toNat) 0
#eval do
  for n in [:65536] do
    unless Nat.popcount n == reference n do throw <| IO.userError s!"popcount mismatch: {n}"
  for k in [63, 64, 65, 127, 128, 255, 256, 4096, 65536] do
    unless (2 ^ k - 1).popcount == k do throw <| IO.userError s!"dense mismatch: {k}"
    unless (2 ^ k).popcount == 1 do throw <| IO.userError s!"sparse mismatch: {k}"
