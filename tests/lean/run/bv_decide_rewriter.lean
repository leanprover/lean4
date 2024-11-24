import Std.Tactic.BVDecide

theorem x_eq_y (x y : Bool) (hx : x = True) (hy : y = True) : x = y := by
  bv_decide

example (z : BitVec 64) : True := by
  let x : BitVec 64 := 10
  let y : BitVec 64 := 20 + z
  have : z + (2 * x) = y := by
    bv_decide
  exact True.intro

example :
  ¬ (0 ≤ 0 + 16#64 ∧ 0 ≤ 0 + 16#64 ∧ (0 + 16#64 ≤ 0 ∨ 0 ≥ 0 + 16#64 ∨ 16#64 = 0 ∨ 16#64 = 0)) := by
  bv_normalize

example (x y z : BitVec 8) (h1 : x = z → False) (h2 : x = y) (h3 : y = z) : False := by
  bv_decide

def mem_subset (a1 a2 b1 b2 : BitVec 64) : Bool :=
  (b2 - b1 = BitVec.ofNat 64 (2^64 - 1)) ||
  ((a2 - b1 <= b2 - b1 && a1 - b1 <= a2 - b1))

-- Show that bv_normalize yields the preprocessed goal
theorem mem_subset_refl : mem_subset a1 a2 a1 a2 := by
  unfold mem_subset
  bv_normalize
  sorry

example {x : BitVec 16} : 0#16 + x = x := by bv_normalize
example {x : BitVec 16} : x + 0#16 = x := by bv_normalize
example {x : BitVec 16} : x.setWidth 16 = x := by bv_normalize
example : (0#w).setWidth 32 = 0#32 := by bv_normalize
example : (0#w).getLsbD i = false := by bv_normalize
example {x : BitVec 0} : x.getLsbD i = false := by bv_normalize
example {x : BitVec 16} {b : Bool} : (x.concat b).getLsbD 0 = b := by bv_normalize
example {x : BitVec 16} : 1 * x = x := by bv_normalize
example {x : BitVec 16} : x * 1 = x := by bv_normalize
example {x : BitVec 16} : ~~~(~~~x) = x := by bv_normalize
example {x : BitVec 16} : x &&& 0 = 0 := by bv_normalize
example {x : BitVec 16} : 0 &&& x = 0 := by bv_normalize
example {x : BitVec 16} : (-1#16) &&& x = x := by bv_normalize
example {x : BitVec 16} : x &&& (-1#16) = x := by bv_normalize
example {x : BitVec 16} : x &&& x = x := by bv_normalize
example {x : BitVec 16} : x &&& ~~~x = 0 := by bv_normalize
example {x : BitVec 16} : ~~~x &&& x = 0 := by bv_normalize
example {x : BitVec 16} : x + ~~~x = -1 := by bv_normalize
example {x : BitVec 16} : ~~~x + x = -1 := by bv_normalize
example {x : BitVec 16} : x + (-x) = 0 := by bv_normalize
example {x : BitVec 16} : (-x) + x = 0 := by bv_normalize
example {x : BitVec 16} : x + x = x * 2 := by bv_normalize
example : BitVec.sshiftRight 0#16 n = 0#16 := by bv_normalize
example {x : BitVec 16} : BitVec.sshiftRight x 0 = x := by bv_normalize
example {x : BitVec 16} : 0#16 * x = 0 := by bv_normalize
example {x : BitVec 16} : x * 0#16 = 0 := by bv_normalize
example {x : BitVec 16} : x <<< 0#16 = x := by bv_normalize
example {x : BitVec 16} : x <<< 0 = x := by bv_normalize
example : 0#16 <<< (n : Nat) = 0 := by bv_normalize
example : 0#16 >>> (n : Nat) = 0 := by bv_normalize
example {x : BitVec 16} : x >>> 0#16 = x := by bv_normalize
example {x : BitVec 16} : x >>> 0 = x := by bv_normalize
example {x : BitVec 16} : 0 < x ↔ (x != 0) := by bv_normalize
example {x : BitVec 16} : ¬(-1#16 < x) := by bv_normalize
example {x : BitVec 16} : BitVec.replicate 0 x = 0 := by bv_normalize
example : BitVec.ofBool true = 1 := by bv_normalize
example : BitVec.ofBool false = 0 := by bv_normalize
example {x : BitVec 16} {i} {h} : x[i] = x.getLsbD i := by bv_normalize
example {x y : BitVec 1} : x + y = x ^^^ y := by bv_normalize
example {x y : BitVec 1} : x * y = x &&& y := by bv_normalize
example {x : BitVec 16} : x / 0 = 0 := by bv_normalize
example {x : BitVec 16} : x % 0 = x := by bv_normalize
example {x : BitVec 16} : ~~~(-x) = x + (-1#16) := by bv_normalize
example {x : BitVec 16} : ~~~(~~~x + 1#16) = x + (-1#16) := by bv_normalize
example {x : BitVec 16} : ~~~(x + 1#16) = ~~~x + (-1#16) := by bv_normalize
example {x : BitVec 16} : ~~~(1#16 + ~~~x) = x + (-1#16) := by bv_normalize
example {x : BitVec 16} : ~~~(1#16 + x) = ~~~x + (-1#16) := by bv_normalize
example {x : BitVec 16} : (10 + x) + 2 = 12 + x := by bv_normalize
example {x : BitVec 16} : (x + 10) + 2 = 12 + x := by bv_normalize
example {x : BitVec 16} : 2 + (x + 10) = 12 + x := by bv_normalize
example {x : BitVec 16} : 2 + (10 + x) = 12 + x := by bv_normalize
example {x : BitVec 16} {b : Bool} : (if b then x else x) = x := by bv_normalize
example {b : Bool} {x : Bool} : (bif b then x else x) = x := by bv_normalize
example {x : BitVec 16} : x.abs = if x.msb then -x else x := by bv_normalize
example : (BitVec.twoPow 16 2) = 4#16 := by bv_normalize
example {x : BitVec 16} : x / (BitVec.twoPow 16 2) = x >>> 2 := by bv_normalize
example {x : BitVec 16} : x / (BitVec.ofNat 16 8) = x >>> 3 := by bv_normalize
example {x y : Bool} (h1 : x && y) : x || y := by bv_normalize

section

example (x y : BitVec 256) : x * y = y * x := by
  bv_decide (config := { acNf := true })

example {x y z : BitVec 64} : ~~~(x &&& (y * z)) = (~~~x ||| ~~~(z * y)) := by
  bv_decide (config := { acNf := true })

end

def foo (x : Bool) : Prop := x = true

example (x : Bool) (h1 h2 : x = true) : foo x := by
  bv_normalize
  have : x = true := by assumption
  sorry
