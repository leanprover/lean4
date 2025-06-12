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

example (a b : Bool) : ((a = true) ↔ (b = true)) ↔ (a == b) := by bv_normalize
example {x : BitVec 16} : 0#16 + x = x := by bv_normalize
example {x : BitVec 16} : x + 0#16 = x := by bv_normalize
example {x : BitVec 16} : x.setWidth 16 = x := by bv_normalize
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
example (x y : BitVec 16) : BitVec.uaddOverflow x y = (x.setWidth (17) + y.setWidth (17)).msb := by bv_normalize
example (x y : BitVec 16) : BitVec.saddOverflow x y = (x.msb = y.msb ∧ ¬(x + y).msb = x.msb) := by bv_normalize
example (x y : BitVec w) : BitVec.uaddOverflow x y = (x.setWidth (w + 1) + y.setWidth (w + 1)).msb := by bv_normalize
example (x y : BitVec w) : BitVec.saddOverflow x y = (x.msb = y.msb ∧ ¬(x + y).msb = x.msb) := by bv_normalize
example (x y : BitVec 16) : BitVec.umulOverflow x y = (BitVec.twoPow 32 16 ≤ x.zeroExtend (32) * y.zeroExtend (32)) := by bv_normalize
example (x y : BitVec 16) : BitVec.smulOverflow x y =
    ((BitVec.signExtend (16 * 2) (BitVec.intMax 16)).slt (BitVec.signExtend (16 * 2) x * BitVec.signExtend (16 * 2) y) ||
    (BitVec.signExtend (16 * 2) x * BitVec.signExtend (16 * 2) y).slt (BitVec.signExtend (16 * 2) (BitVec.intMin 16))) :=
  by bv_normalize
example (x y : BitVec w) : BitVec.umulOverflow x y = (0 < w && BitVec.twoPow (w * 2) w ≤ x.zeroExtend (w * 2) * y.zeroExtend (w * 2)) := by bv_normalize
example (x y : BitVec w) : BitVec.smulOverflow x y =
    (decide (0 < w) &&
    ((BitVec.signExtend (w * 2) (BitVec.intMax w)).slt (BitVec.signExtend (w * 2) x * BitVec.signExtend (w * 2) y) ||
    (BitVec.signExtend (w * 2) x * BitVec.signExtend (w * 2) y).slt (BitVec.signExtend (w * 2) (BitVec.intMin w))))
  := by bv_normalize

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

-- bv_equal_const_not
example (a : BitVec 32) : (~~~a = 0#32) ↔ (a = -1) := by
  bv_normalize

example (a : BitVec 32) : (0#32 = ~~~a) ↔ (a = -1) := by
  bv_normalize

-- reducing or to and while still applying or specific rewrites
example {x : BitVec 64} : x ||| 0 = x := by
  bv_normalize

-- bv_and_eq_allOnes
example (a b : BitVec 16) : (a &&& b == -1#16) = (a == -1#16 && b == -1#16) := by
  bv_normalize

example (a b : BitVec 16) : (-1#16 == a &&& b) = (a == -1#16 && b == -1#16) := by
  bv_normalize

-- extractLsb'_and
example (a b : BitVec 16) :
    BitVec.extractLsb' 1 12 (a &&& b) = BitVec.extractLsb' 1 12 a &&& BitVec.extractLsb' 1 12 b := by
  bv_normalize

-- extractLsb'_xor
example (a b : BitVec 16) :
    BitVec.extractLsb' 1 12 (a ^^^ b) = BitVec.extractLsb' 1 12 a ^^^ BitVec.extractLsb' 1 12 b := by
  bv_normalize

-- extractLsb'_not_of_lt
example (a b : BitVec 16) :
    BitVec.extractLsb' 1 12 (~~~(a &&& b)) = ~~~(BitVec.extractLsb' 1 12 a &&& BitVec.extractLsb' 1 12 b) := by
  bv_normalize

-- extractLsb'_if
example (a b : BitVec 16) (c : Bool) :
    BitVec.extractLsb' 1 12 (if c then a else b) = if c then BitVec.extractLsb' 1 12 a else BitVec.extractLsb' 1 12 b := by
  bv_normalize

-- extractLsb full
example (a : BitVec 16) : a.extractLsb' 0 16 = a := by
  bv_normalize

example (a : BitVec 16) : a.extractLsb 15 0 = a := by
  bv_normalize

-- mul with twoPow
example (a : BitVec 16) : 8#16 * a = a <<< 3 := by
  bv_normalize

example (a : BitVec 16) : a * 8#16 = a <<< 3 := by
  bv_normalize

example (a : BitVec 16) : a + a = a <<< 1 := by
  bv_normalize

-- NOT_EQUAL_BV1_BOOL
example : ∀ (a : Bool), (!(a == true)) = (!a) := by
  bv_normalize

example : ∀ (a : Bool), (!(a == false)) = a := by
  bv_normalize

example : ∀ (a : Bool), (!(true == a)) = !a := by
  bv_normalize

example : ∀ (a : Bool), (!(false == a)) = a := by
  bv_normalize

example : ∀ (a : BitVec 1), (!(a == 1#1)) = (a == 0#1) := by
  bv_normalize

example : ∀ (a : BitVec 1), (!(a == 0#1)) = (a == 1#1) := by
  bv_normalize

example : ∀ (a : BitVec 1), (!(1#1 == a)) = (a == 0#1) := by
  bv_normalize

example : ∀ (a : BitVec 1), (!(0#1 == a)) = (a == 1#1) := by
  bv_normalize

-- ITE_SAME
example : ∀ (c t e : Bool), ((bif c then t else e) == t) = (c || (t == e)) := by
  bv_normalize

example : ∀ (c t e : Bool), (t == (bif c then t else e)) = (c || (t == e)) := by
  bv_normalize

example : ∀ (c t e : Bool), ((bif c then t else e) == e) = (!c || (t == e)) := by
  bv_normalize

example : ∀ (c t e : Bool), (e == (bif c then t else e)) = (!c || (t == e)) := by
  bv_normalize

example : ∀ (c : Bool) (t e : BitVec 8), ((bif c then t else e) == t) = (c || (t == e)) := by
  bv_normalize

example : ∀ (c : Bool) (t e : BitVec 8), (t == (bif c then t else e)) = (c || (t == e)) := by
  bv_normalize

example : ∀ (c : Bool) (t e : BitVec 8), ((bif c then t else e) == e) = (!c || (t == e)) := by
  bv_normalize

example : ∀ (c : Bool) (t e : BitVec 8), (e == (bif c then t else e)) = (!c || (t == e)) := by
  bv_normalize

example (c : Bool) : ((if c then 1#1 else 0#1) == 1#1) ↔ c := by
  bv_normalize

-- ITE_THEN_ITE_1
example (cond : Bool) {a b c d : Bool}
    (h : (bif cond then (bif cond then a else b) else c) = d) :
    (bif cond then a else c) = d := by
  bv_normalize

example (cond : Bool) {a b c d : Bool}
    (h : (bif cond then !(bif cond then a else b) else c) = d) :
    (bif cond then !a else c) = d := by
  bv_normalize

example (cond : Bool) {a b c d : BitVec 8}
    (h : (bif cond then ~~~(bif cond then a else b) else c) = d) :
    (bif cond then ~~~a else c) = d := by
  bv_normalize

-- ITE_ELSE_ITE_1
example (cond : Bool) {a b c d : Bool}
    (h : (bif cond then a else (bif cond then b else c)) = d) :
    (bif cond then a else c) = d := by
  bv_normalize

example (cond : Bool) {a b c d : Bool}
    (h : (bif cond then a else !(bif cond then b else c)) = d) :
    (bif cond then a else !c) = d := by
  bv_normalize

example (cond : Bool) {a b c d : BitVec 8}
    (h : (bif cond then a else ~~~(bif cond then b else c)) = d) :
    (bif cond then a else ~~~c) = d := by
  bv_normalize

-- ITE_THEN_ITE_2
example (c0 c1 : Bool) {a b d : Bool}
    (h : (bif c0 then (bif c1 then a else b) else a) = d) :
    (bif c0 && !c1 then b else a) = d := by
  bv_normalize

example (c0 c1 : Bool) {a b d : Bool}
    (h : (bif c0 then !(bif c1 then !a else b) else a) = d) :
    (bif c0 && !c1 then !b else a) = d := by
  bv_normalize

example (c0 c1 : Bool) {a b d : BitVec 8}
    (h : (bif c0 then ~~~(bif c1 then ~~~a else b) else a) = d) :
    (bif c0 && !c1 then ~~~b else a) = d := by
  bv_normalize

-- ITE_ELSE_ITE_2
example (c0 c1 : Bool) {a b d : Bool}
    (h : (bif c0 then a else (bif c1 then a else b)) = d) :
    (bif !c0 && !c1 then b else a) = d := by
  bv_normalize

example (c0 c1 : Bool) {a b d : Bool}
    (h : (bif c0 then a else !(bif c1 then !a else b)) = d) :
    (bif !c0 && !c1 then !b else a) = d := by
  bv_normalize

example (c0 c1 : Bool) {a b d : BitVec 8}
    (h : (bif c0 then a else ~~~(bif c1 then ~~~a else b)) = d) :
    (bif !c0 && !c1 then ~~~b else a) = d := by
  bv_normalize

-- ITE_THEN_ITE_3
example (c0 c1 : Bool) {a b d : Bool}
    (h : (bif c0 then (bif c1 then b else a) else a) = d) :
    (bif c0 && c1 then b else a) = d := by
  bv_normalize

example (c0 c1 : Bool) {a b d : Bool}
    (h : (bif c0 then !(bif c1 then b else !a) else a) = d) :
    (bif c0 && c1 then !b else a) = d := by
  bv_normalize

example (c0 c1 : Bool) {a b d : BitVec 8}
    (h : (bif c0 then ~~~(bif c1 then b else ~~~a) else a) = d) :
    (bif c0 && c1 then ~~~b else a) = d := by
  bv_normalize

-- ITE_ELSE_ITE_3
example (c0 c1 : Bool) {a b d : Bool}
    (h : (bif c0 then a else (bif c1 then b else a)) = d) :
    (bif !c0 && c1 then b else a) = d := by
  bv_normalize

example (c0 c1 : Bool) {a b d : Bool}
    (h : (bif c0 then a else !(bif c1 then b else !a)) = d) :
    (bif !c0 && c1 then !b else a) = d := by
  bv_normalize

example (c0 c1 : Bool) {a b d : BitVec 8}
    (h : (bif c0 then a else ~~~(bif c1 then b else ~~~a)) = d) :
    (bif !c0 && c1 then ~~~b else a) = d := by
  bv_normalize

-- BV_MUL_ITE
example {c : Bool} {a e : BitVec 8} :
    (a * (bif c then 0#8 else e)) = (bif c then 0#8 else a * e) := by
  bv_normalize

example {c : Bool} {a t : BitVec 8} :
    (a * (bif c then t else 0#8)) = (bif c then a * t else 0#8) := by
  bv_normalize

example {c : Bool} {a e : BitVec 8} :
    ((bif c then 0#8 else e) * a) = (bif c then 0#8 else e * a) := by
  bv_normalize

example {c : Bool} {a t : BitVec 8} :
    ((bif c then t else 0#8) * a) = (bif c then t * a else 0#8) := by
  bv_normalize

-- EQAL_CONST_BV1
example {b : Bool} {a : BitVec 1} :
    ((a == 1#1) == b) = (a == bif b then 1#1 else 0#1) := by
  bv_normalize

example {b : Bool} {a : BitVec 1} :
    ((1#1 == a) == b) = (a == bif b then 1#1 else 0#1) := by
  bv_normalize

example {b : Bool} {a : BitVec 1} :
    (b == (a == 1#1)) = (a == bif b then 1#1 else 0#1) := by
  bv_normalize

example {b : Bool} {a : BitVec 1} :
    (b == (1#1 == a)) = (a == bif b then 1#1 else 0#1) := by
  bv_normalize

example {b : Bool} {a : BitVec 1} :
    ((a == 0#1) == b) = (a == bif b then 0#1 else 1#1) := by
  bv_normalize

example {b : Bool} {a : BitVec 1} :
    ((0#1 == a) == b) = (a == bif b then 0#1 else 1#1) := by
  bv_normalize

example {b : Bool} {a : BitVec 1} :
    (b == (a == 0#1)) = (a == bif b then 0#1 else 1#1) := by
  bv_normalize

example {b : Bool} {a : BitVec 1} :
    (b == (0#1 == a)) = (a == bif b then 0#1 else 1#1) := by
  bv_normalize

-- EQUAL_ITE_SAME
example {c d : Bool} {a b : BitVec 8}
    (h : (a == bif c then a else b) = d) :
    (c || (a == b)) = d := by
  bv_normalize

example {c d : Bool} {a b : BitVec 8}
    (h : (a == bif c then b else a) = d) :
    (!c || (b == a)) = d := by
  bv_normalize

example {c d : Bool} {a b : BitVec 8}
    (h : ((bif c then a else b) == a) = d) :
    (c || (a == b)) = d := by
  bv_normalize

example {c d : Bool} {a b : BitVec 8}
    (h : ((bif c then b else a) == a) = d) :
    (!c || (b == a)) = d := by
  bv_normalize

-- EQUAL_ITE_INVERTED
example {a b c : Bool} : (a == !bif c then a else b) = (!c && (a == !b)) := by
  bv_normalize

example {a b c : Bool} : (a == !bif c then b else a) = (c && (a == !b)) := by
  bv_normalize

example {a b c : Bool} : ((!bif c then a else b) == a) = (!c && (a == !b)) := by
  bv_normalize

example {a b c : Bool} : ((!bif c then b else a) == a) = (c && (a == !b)) := by
  bv_normalize

example {a b : BitVec 8} {c : Bool} :
    (a == ~~~bif c then a else b) = (!c && (a == ~~~b)) := by
  bv_normalize

example {a b : BitVec 8} {c : Bool} :
    (a == ~~~bif c then b else a) = (c && (a == ~~~b)) := by
  bv_normalize

example {a b : BitVec 8} {c : Bool} :
    ((~~~bif c then a else b) == a) = (!c && (~~~b == a)) := by
  bv_normalize

example {a b : BitVec 8} {c : Bool} :
    ((~~~bif c then b else a) == a) = (c && (~~~b == a)) := by
  bv_normalize

-- remove casts
example {a : BitVec 8} : a = a.cast rfl := by
  bv_normalize

-- BitVec.mul_neg
example {a : BitVec 8} : a * -1 = -a := by bv_normalize
example {a : BitVec 8} : -1 * a = -a := by bv_normalize
example {a : BitVec 8} : -1 * a + a = 0 := by bv_normalize
example {a : BitVec 8} : a + -1 * a = 0 := by bv_normalize

-- SHR_CONST
example {a : BitVec 8} : a >>> 1 = 0#1 ++ BitVec.extractLsb' 1 7 a := by bv_normalize
example {a : BitVec 8} : a >>> 3 = 0#3 ++ BitVec.extractLsb' 3 5 a := by bv_normalize
example {a : BitVec 8} : a >>> 8 = 0 := by bv_normalize
example {a : BitVec 8} : a >>> 12 = 0 := by bv_normalize

-- SHL_CONST
example {a : BitVec 8} : a <<< 1 = BitVec.extractLsb' 0 7 a ++ 0#1 := by bv_normalize
example {a : BitVec 8} : a <<< 3 = BitVec.extractLsb' 0 5 a ++ 0#3 := by bv_normalize
example {a : BitVec 8} : a <<< 8 = 0 := by bv_normalize
example {a : BitVec 8} : a <<< 12 = 0 := by bv_normalize

-- EQUAL_CONST_BV_ADD
example {a : BitVec 8} (h : a + 5 = 7) : a = 2 := by bv_normalize
example {a : BitVec 8} (h : 5 + a = 7) : a = 2 := by bv_normalize
example {a : BitVec 8} (h : 7 = a + 5) : a = 2 := by bv_normalize
example {a : BitVec 8} (h : 7 = 5 + a) : a = 2 := by bv_normalize

-- BV_AND_CONST
example {x : BitVec 8} : (10 &&& x) &&& 2 = 2 &&& x := by bv_normalize
example {x : BitVec 8} : (x &&& 10) &&& 2 = 2 &&& x := by bv_normalize
example {x : BitVec 8} : 2 &&& (x &&& 10) = 2 &&& x := by bv_normalize
example {x : BitVec 8} : 2 &&& (10 &&& x) = 2 &&& x := by bv_normalize

-- BV_CONCAT_CONST
example {x : BitVec 8} : 8#4 ++ (4#4 ++ x) = 132#8 ++ x := by bv_normalize
example {x : BitVec 8} : (x ++ 4#4) ++ 8#4 = x ++ 72#8 := by bv_normalize

-- BV_CONCAT_EXTRACT
example {x : BitVec 8} : x.extractLsb' 3 5 ++ x.extractLsb' 1 2 = x.extractLsb' 1 7 := by
  bv_normalize

example {x : BitVec 8} :
    (~~~x.extractLsb' 3 5) ++ (~~~x.extractLsb' 1 2) = ~~~x.extractLsb' 1 7 := by
  bv_normalize

-- BV_ULT_SPECIAL_CONST
example {x : BitVec 8} : x < 255 ↔ x ≠ 255 := by bv_normalize

-- BV_SIGN_EXTEND_ELIM
example {x : BitVec 8} : x.signExtend 16 = (bif x.msb then 255#8 else 0#8) ++ x := by bv_normalize
example {x : BitVec 8} : x.signExtend 4 = BitVec.extractLsb' 0 4 x := by bv_normalize

-- BV_ADD_NEG_MUL
example {x y : BitVec 8} : -(x + x * y) = x * ~~~y := by bv_normalize
example {x y : BitVec 8} : -(x + y * x) = ~~~y * x := by bv_normalize
example {x y : BitVec 8} : -(x * y + x) = x * ~~~y := by bv_normalize
example {x y : BitVec 8} : -(y * x + x) = ~~~y * x := by bv_normalize
example {x y : BitVec 8} : 1#8 + ~~~(x + x * y) = x * ~~~y := by bv_normalize
example {x y : BitVec 8} : 1#8 + ~~~(x + y * x) = ~~~y * x := by bv_normalize
example {x y : BitVec 8} : 1#8 + ~~~(x * y + x) = x * ~~~y := by bv_normalize
example {x y : BitVec 8} : 1#8 + ~~~(y * x + x) = ~~~y * x := by bv_normalize
example  : ∀ (s t : BitVec 32), (!!-(t + s * t) == ~~~s * t) = true := by
  bv_normalize (config  := {acNf := true})

-- BV_EXTRACT_CONCAT
example {x y : BitVec 8} : BitVec.extractLsb' 0 4 (x ++ y) = BitVec.extractLsb' 0 4 y := by
  bv_normalize

example {x y : BitVec 8} : BitVec.extractLsb' 8 4 (x ++ y) = BitVec.extractLsb' 0 4 x := by
  bv_normalize

-- NORM_BV_ADD_MUL
example {x y : BitVec 8} : ~~~(x * ~~~y) + 1#8 = x + (x * y) := by bv_normalize
example {x y : BitVec 8} : ~~~(~~~y * x) + 1#8 = x + (y * x) := by bv_normalize
example {x y : BitVec 8} : 1#8 + ~~~(x * ~~~y) = x + (x * y) := by bv_normalize
example {x y : BitVec 8} : 1#8 + ~~~(~~~y * x) = x + (y * x) := by bv_normalize
example {x y : BitVec 8} : -(x * ~~~y) = x + (x * y) := by bv_normalize

-- NORM_BV_SHL_NEG
example {x y : BitVec 8} : (~~~x + 1) <<< y = ~~~(x <<< y) + 1 := by bv_normalize
example {x y : BitVec 8} : (1 + ~~~x) <<< y = ~~~(x <<< y) + 1 := by bv_normalize
example {x y : BitVec 8} : (-x) <<< y = -(x <<< y) := by bv_normalize

example {x : BitVec 16} : (x = BitVec.allOnes 16) → (BitVec.uaddOverflow x x) := by bv_decide

example {x : BitVec 64} : (x = BitVec.intMin 64) ↔ (BitVec.negOverflow x) := by bv_decide

example {x : BitVec 16} : (x = BitVec.allOnes 16) → (BitVec.umulOverflow x x) := by bv_decide

example {x : BitVec 8} : (x = -32#8) → (BitVec.smulOverflow x x) := by bv_decide

example {x : BitVec 8} : (x = 0#8) → (¬ BitVec.smulOverflow x x) := by bv_decide

example {x : BitVec 8} : (x ≥ -2#8) → (¬ BitVec.smulOverflow x x) := by bv_decide

example {x : BitVec 8} : (x < 12#8) → (¬ BitVec.smulOverflow x x) := by bv_decide

example {x y : BitVec 64} : ((x = 0#64) ∧ (y = BitVec.allOnes 64)) → (BitVec.usubOverflow x y) := by bv_decide

example {x y : BitVec 64} : ((x = BitVec.twoPow 64 62) ∧ (y = BitVec.twoPow 64 63)) → (BitVec.ssubOverflow x y) := by bv_decide

example {x y : BitVec 64} : ((x = BitVec.intMin 64) ∧ (y = BitVec.allOnes 64)) ↔ (BitVec.sdivOverflow x y) := by bv_decide

example {x : BitVec 5} : (x.setWidth' (show 5 ≤ 6 by omega)).setWidth 5  = x := by bv_decide

-- BV_EXTRACT_ADD_MUL
example {x y : BitVec 8} :
    BitVec.extractLsb' 0 4 (x + y) = BitVec.extractLsb' 0 4 x + BitVec.extractLsb' 0 4 y := by
  bv_normalize

example {x y : BitVec 8} :
    BitVec.extractLsb' 0 4 (x * y) = BitVec.extractLsb' 0 4 x * BitVec.extractLsb' 0 4 y := by
  bv_normalize

-- BV_ADD_SHL
example {x y : BitVec 8} : x + (y <<< x) = x ||| (y <<< x) := by bv_normalize
example {x y : BitVec 8} : (y <<< x) + x = (y <<< x) ||| x := by bv_normalize

-- NORM_BV_ADD_CONCAT
example {x : BitVec 8} {y : BitVec 3} : (x ++ 0#3) + (0#8 ++ y) = x ++ y := by bv_normalize
example {x : BitVec 8} {y : BitVec 3} : (0#3 ++ x) + (y ++ 0#8) = y ++ x := by bv_normalize

-- CLZ
example {x : BitVec 8} (h : x = 0#8) : x.clz = 8 := by bv_decide
example {x : BitVec 8} (h : ¬ x = 0#8) : (x >>> 1).clz = x.clz + 1 := by bv_decide
example {x y : BitVec 8} : x.clz < y.clz → y < x := by bv_decide
example {x : BitVec 8} : x.clz ≤ 8 := by bv_decide

section

namespace NormalizeMul
/- Test examples of the multiplication normalizer -/

/-- This example does not yet work,
  since we do not have the full Bitwuzla algorithm. -/
example {x y z : BitVec 64} : ~~~(x &&& (y * z)) = (~~~x ||| ~~~(z * y)) := by
  sorry
example (x y : BitVec 256) : x * y = y * x := by
  bv_decide (config := { acNf := true })
example (x y : BitVec 256) : x * y * z = z * y * x := by
  bv_decide (config := { acNf := true })
example (x y : BitVec 256) : x * y * z = z * y * x := by
  bv_decide (config := { acNf := true })



end NormalizeMul

def foo (x : Bool) : Prop := x = true

example (x : Bool) (h1 h2 : x = true) : foo x := by
  bv_normalize
  have : x = true := by assumption
  sorry
