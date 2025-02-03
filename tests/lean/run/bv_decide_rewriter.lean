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
example {x : BitVec 16} : x >>> (12 : Nat) = x >>> 12#16 := by bv_normalize
example {x : BitVec 16} : x <<< (12 : Nat) = x <<< 12#16 := by bv_normalize
example {x : BitVec 16} : x.sshiftRight (12 : Nat) = x.sshiftRight' 12#16 := by bv_normalize
example {x : BitVec 16} : x <<< 0#16 = x := by bv_normalize
example {x : BitVec 16} : x <<< 0 = x := by bv_normalize
example : 0#16 <<< (n : Nat) = 0 := by bv_normalize
example : 0#16 >>> (n : Nat) = 0 := by bv_normalize
example {x : BitVec 16} : x >>> 0#16 = x := by bv_normalize
example {x : BitVec 16} : x >>> 0 = x := by bv_normalize
example {x : BitVec 16} : 0 < x ↔ (x != 0) := by bv_normalize
example {x : BitVec 16} : ¬(65535#16 < x) := by bv_normalize
example {x : BitVec 16} : ¬(-1#16 < x) := by bv_normalize
example {x : BitVec 16} : BitVec.replicate 0 x = 0 := by bv_normalize
example : BitVec.ofBool true = 1 := by bv_normalize
example : BitVec.ofBool false = 0 := by bv_normalize
example {x : BitVec 16} {i} {h} : x[i] = x.getLsbD i := by bv_normalize
example {x y : BitVec 1} : x + y = x ^^^ y := by bv_normalize
example {x y : BitVec 1} : x * y = x &&& y := by bv_normalize
example {x : BitVec 16} : x / 0 = 0 := by bv_normalize
example {x : BitVec 16} : x % 0 = x := by bv_normalize
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
example (a b c: Bool) : (if a then b else c) = (if !a then c else b) := by bv_normalize

-- not_neg
example {x : BitVec 16} : ~~~(-x) = x + (-1#16) := by bv_normalize
example {x : BitVec 16} : ~~~(~~~x + 1#16) = x + (-1#16) := by bv_normalize
example {x : BitVec 16} : ~~~(x + 1#16) = ~~~x + (-1#16) := by bv_normalize
example {x : BitVec 16} : ~~~(1#16 + ~~~x) = x + (-1#16) := by bv_normalize
example {x : BitVec 16} : ~~~(1#16 + x) = ~~~x + (-1#16) := by bv_normalize

-- add_neg / neg_add
example (x : BitVec 16) : x + -x = 0 := by bv_normalize
example (x : BitVec 16) : x - x = 0 := by bv_normalize
example (x : BitVec 16) : x + (~~~x + 1) = 0 := by bv_normalize
example (x : BitVec 16) : x + (1 + ~~~x) = 0 := by bv_normalize
example (x : BitVec 16) : -x + x = 0 := by bv_normalize
example (x : BitVec 16) : (~~~x + 1) + x = 0 := by bv_normalize
example (x : BitVec 16) : (1 + ~~~x) + x = 0 := by bv_normalize

-- neg_mul / mul_neg
example (x y : BitVec 16) : (-x) * y = -(x * y) := by bv_normalize
example (x y : BitVec 16) : x * (-y) = -(x * y) := by bv_normalize
example (x y : BitVec 16) : -x * -y = x * y := by bv_normalize
example (x y : BitVec 16) : (~~~x + 1) * y = ~~~(x * y) + 1 := by bv_normalize
example (x y : BitVec 16) : (1 + ~~~x) * y = ~~~(x * y) + 1 := by bv_normalize
example (x y : BitVec 16) : x * (~~~y + 1) = ~~~(x * y) + 1 := by bv_normalize
example (x y : BitVec 16) : x * (1 + ~~~y) = ~~~(x * y) + 1 := by bv_normalize
example (x y : BitVec 16) : (~~~x + 1) * (~~~y + 1) = x * y := by bv_normalize
example (x y : BitVec 16) : (1 + ~~~x) * (~~~y + 1) = x * y := by bv_normalize
example (x y : BitVec 16) : (1 + ~~~x) * (1 + ~~~y) = x * y := by bv_normalize

-- lt_irrefl
example (x : BitVec 16) : ¬x < x := by bv_normalize
example (x : BitVec 16) : !(x.ult x) := by bv_normalize
example (x : BitVec 16) : !(x.slt x) := by bv_normalize

-- not_lt_zero
example (x : BitVec 16) : ¬x < 0 := by bv_normalize
example (x : BitVec 16) : x ≥ 0 := by bv_normalize
example (x : BitVec 16) : !(x.ult 0) := by bv_normalize

-- lt_one_iff
example (x : BitVec 16) : (x < 1) ↔ (x = 0) := by bv_normalize
example (x : BitVec 16) : (x.ult 1) = (x == 0) := by bv_normalize

-- ushiftRight_self
example (x : BitVec 16) : (x >>> x) == 0 := by bv_normalize

-- add_left_inj / add_right_inj
example (x y z : BitVec 16) : (x + z == y + z) = (x == y) := by bv_normalize
example (x y z : BitVec 16) : (x + z == z + y) = (x == y) := by bv_normalize
example (x y z : BitVec 16) : (z + x == y + z) = (x == y) := by bv_normalize
example (x y z : BitVec 16) : (z + x == z + y) = (x == y) := by bv_normalize

-- add_left_eq_self / add_right_eq_self
example (x y : BitVec 16) : (x + y == x) = (y == 0) := by bv_normalize
example (x y : BitVec 16) : (x + y == y) = (x == 0) := by bv_normalize
example (x y : BitVec 16) : (x == x + y) = (y == 0) := by bv_normalize
example (x y : BitVec 16) : (x == y + x) = (y == 0) := by bv_normalize

-- eq_sub_iff_add_eq / sub_eq_iff_eq_add
example (x y z : BitVec 16) : (x + -y == z) = (x == z + y) := by bv_normalize
example (x y z : BitVec 16) : (x - y == z) = (x == z + y) := by bv_normalize
example (x y z : BitVec 16) : (x + (~~~y + 1) == z) = (x == z + y) := by bv_normalize
example (x y z : BitVec 16) : (x + (1 + ~~~y) == z) = (x == z + y) := by bv_normalize
example (x y z : BitVec 16) : (-x + y == z) = (y == z + x) := by bv_normalize
example (x y z : BitVec 16) : ((~~~x + 1) + y == z) = (y == z + x) := by bv_normalize
example (x y z : BitVec 16) : ((1 + ~~~x) + y == z) = (y == z + x) := by bv_normalize
example (x y z : BitVec 16) : (z == x + -y) = (z + y == x) := by bv_normalize
example (x y z : BitVec 16) : (z == x - y) = (z + y == x) := by bv_normalize
example (x y z : BitVec 16) : (z == x + (~~~y + 1)) = (z + y == x) := by bv_normalize
example (x y z : BitVec 16) : (z == x + (1 + ~~~y)) = (z + y == x) := by bv_normalize
example (x y z : BitVec 16) : (z == -x + y) = (z + x == y) := by bv_normalize
example (x y z : BitVec 16) : (z == (~~~x + 1) + y) = (z + x == y) := by bv_normalize
example (x y z : BitVec 16) : (z == (1 + ~~~x) + y) = (z + x == y) := by bv_normalize

-- or_beq_zero_iff
example (x y : BitVec 16) : (x ||| y == 0) = (x == 0 && y == 0) := by bv_normalize
example (x y : BitVec 16) : (0 == x ||| y) = (x == 0 && y == 0) := by bv_normalize

-- xor_beq_zero_iff
example (x y : BitVec 16) : (x ^^^ y == 0) = (x == y) := by bv_normalize
example (x y : BitVec 16) : (0 == x ^^^ y) = (x == y) := by bv_normalize

-- xor_left_inj / xor_right_inj
example (x y z : BitVec 16) : (x ^^^ z == y ^^^ z) = (x == y) := by bv_normalize
example (x y z : BitVec 16) : (x ^^^ z == z ^^^ y) = (x == y) := by bv_normalize
example (x y z : BitVec 16) : (z ^^^ x == y ^^^ z) = (x == y) := by bv_normalize
example (x y z : BitVec 16) : (z ^^^ x == z ^^^ y) = (x == y) := by bv_normalize

-- bif_eq_bif
example (d a b c : Bool) :
    ((bif d then a else b) == (bif d then a else c)) = (d || (b == c)) := by
  bv_normalize

example (d a b c : Bool) :
    ((!(bif d then a else b)) == (bif d then a else c)) = (!d && (!b) == c) := by
  bv_normalize

example (d a b c : Bool) :
    ((bif d then a else b) == !(bif d then a else c)) = (!d && b == (!c)) := by
  bv_normalize

example (d a b c : Bool) :
    ((bif d then a else c) == (bif d then b else c)) = (!d || a == b) := by
  bv_normalize

example (d a b c : Bool) :
    ((!(bif d then a else c)) == (bif d then b else c)) = (d && (!a) == b) := by
  bv_normalize

example (d a b c : Bool) :
    ((bif d then a else c) == !(bif d then b else c)) = (d && a == (!b)) := by
  bv_normalize

example (a b c d e : BitVec 16) :
    ((bif a == b then c else d) == (bif a == b then c else e)) = (a == b || d == e) := by
  bv_normalize

example (a b c d e : BitVec 16) :
    ((bif a == b then c else d) == (bif a == b then e else d)) = (!a == b || c == e) := by
  bv_normalize

example (d : Bool) (a b c : BitVec w) :
    ((bif d then a else b) == (bif d then a else c)) = (d || b == c) := by
  cases d <;> simp

example (d : Bool) (a b c : BitVec w) :
    (~~~(bif d then a else b) == (bif d then a else c)) = (bif d then ~~~a == a else ~~~b == c) := by
  bv_normalize

example (d : Bool) (a b c : BitVec w) :
    ((bif d then a else b) == ~~~(bif d then a else c)) = (bif d then a == ~~~a else b == ~~~c) := by
  bv_normalize

example (d : Bool) (a b c : BitVec w) :
    ((bif d then a else c) == (bif d then b else c)) = (!d || a == b) := by
  bv_normalize

example (d : Bool) (a b c : BitVec w) :
    (~~~(bif d then a else c) == (bif d then b else c)) = (bif d then ~~~a == b else ~~~c == c) := by
  bv_normalize

example (d : Bool) (a b c : BitVec w) :
    ((bif d then a else c) == ~~~(bif d then b else c)) = (bif d then a == ~~~b else c == ~~~c) := by
  bv_normalize

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
