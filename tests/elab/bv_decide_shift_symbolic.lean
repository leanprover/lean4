module
meta import Std.Tactic.BVDecide
import Std.Tactic.BVDecide

/-!
Tests for `bv_decide` support for shifts by symbolic `Nat` amounts and for `BitVec.extractLsb'`
at a symbolic start offset. These are handled by clamping the amount into a `BitVec` via
`BitVec.ofNatClamp`, so that only the amount becomes an uninterpreted atom while the shift
structure stays visible to the bitblaster.
-/

section UShiftRight

example (x y : BitVec 64) (n : Nat) : (x &&& y) >>> n = (x >>> n) &&& (y >>> n) := by
  bv_decide

example (x y : BitVec 64) (n : Nat) : (x ||| y) >>> n = (x >>> n) ||| (y >>> n) := by
  bv_decide

example (x : BitVec 16) (n m : Nat) : x >>> n >>> m = x >>> m >>> n := by
  bv_decide

example (x : BitVec 16) (n : Nat) (h : x = 0) : x >>> n = 0 := by
  bv_decide

example (x : BitVec 16) (n : Nat) : x >>> n ≤ x := by
  bv_decide

end UShiftRight

section ShiftLeft

example (x y : BitVec 64) (n : Nat) : (x &&& y) <<< n = (x <<< n) &&& (y <<< n) := by
  bv_decide

example (x : BitVec 16) (n : Nat) (h : x = 0) : x <<< n = 0 := by
  bv_decide

end ShiftLeft

section SshiftRight

example (x y : BitVec 16) (n : Nat) :
    (x &&& y).sshiftRight n = (x.sshiftRight n) &&& (y.sshiftRight n) := by
  bv_decide

example (n : Nat) : (BitVec.allOnes 16).sshiftRight n = BitVec.allOnes 16 := by
  bv_decide

example (x : BitVec 16) (n : Nat) (h : x.msb = false) : x.sshiftRight n = x >>> n := by
  bv_decide

example (x : BitVec 16) (h : BitVec.slt 0 x) (n : Nat) : x.sshiftRight n ≤ x := by
  bv_decide

end SshiftRight

section ExtractLsb'

example (x y : BitVec 64) (n : Nat) :
    (x &&& y).extractLsb' n 8 = (x.extractLsb' n 8) &&& (y.extractLsb' n 8) := by
  bv_decide

example (x : BitVec 64) (n : Nat) : x.extractLsb' n 64 = x >>> n := by
  bv_decide

example (x : BitVec 64) (n : Nat) : (x >>> n).setWidth 8 = x.extractLsb' n 8 := by
  bv_decide

example (x : BitVec 64) (n : Nat) : x.extractLsb' n 8 = (x >>> n).extractLsb' 0 8 := by
  bv_decide

end ExtractLsb'

section Constant

-- Shifts by constant `Nat` amounts keep working.
example (x : BitVec 64) : x >>> 65 = 0 := by bv_decide
example (x : BitVec 64) : x <<< 65 = 0 := by bv_decide

-- Shifts by `BitVec` literals of a different width than the shifted value used to fail with an
-- internal error and are now eliminated like same-width literal shifts.
example (x : BitVec 8) : x >>> (2 : BitVec 4) = x >>> 2 := by bv_decide
example (x : BitVec 8) : x <<< (2 : BitVec 4) = x <<< 2 := by bv_decide
example (x : BitVec 8) : x.sshiftRight' (1#2) = x.sshiftRight 1 := by bv_decide

end Constant

-- A false goal produces a counterexample mentioning the clamped shift amount instead of crashing.
/--
error: The prover found a potentially spurious counterexample:
- It abstracted the following unsupported expressions as opaque variables:
  - BitVec.ofNatClamp 4 n
Consider the following assignment:
x = 255#8
BitVec.ofNatClamp 4 n = 15#4
-/
#guard_msgs in
example (x : BitVec 8) (n : Nat) : x >>> n = x := by
  bv_decide
