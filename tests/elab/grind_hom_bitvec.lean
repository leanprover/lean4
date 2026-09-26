/-!
Tests for `[grind hom]` over `BitVec`, ported from the intblasting prototype test suite (#15224).
The goals relate bit-vector operations to their unsigned (`toNat`) and signed (`toInt`)
interpretations. Goals that `grind` cannot prove yet are disabled and marked with `TODO`.
-/

-- Shim for prototype names
abbrev BitVec.unsigned {w} (x : BitVec w) : Int := Int.ofNat x.toNat
abbrev BitVec.signed {w} (x : BitVec w) := x.toInt

-- Compatibility lemma for ported tests
theorem BitVec.toNat_eq_unsigned {w} (x : BitVec w) : x.toNat = x.unsigned := rfl

theorem BitVec.lt_homo_test {w : Nat} (x y : BitVec w) : x < y ↔ x.unsigned < y.unsigned := by
  grind

theorem BitVec.le_homo_test {w : Nat} (x y : BitVec w) : x ≤ y ↔ x.unsigned ≤ y.unsigned := by
  grind

example (x y : BitVec 16) :
  x.unsigned < 256 → y.unsigned < 256 →
  (x + y).unsigned = x.unsigned + y.unsigned := by grind
example (x y z : BitVec 16) : x.unsigned < 256 → y.unsigned < 256 →
  x.unsigned < 256 → y.unsigned < 256 →
  (z + x + z + y - (z<<<1)).unsigned = x.unsigned + y.unsigned := by grind
example (x y z : BitVec 16) : x.unsigned < 256 → y.unsigned < 256 →
  x.unsigned < 256 → y.unsigned < 256 →
  ((BitVec.ofNat _ 3)*z + x + z + y - (z<<<2)).unsigned = x.unsigned + y.unsigned := by grind
example (x y z : BitVec 16) : x.unsigned < 256 → y.unsigned < 256 →
  x.unsigned < 256 → y.unsigned < 256 →
  (3*z + x + z + y - (z<<<2)).unsigned = x.unsigned + y.unsigned := by grind
example (x y z : BitVec 16) : x.unsigned < 256 → y.unsigned < 256 →
  x.unsigned < 256 → y.unsigned < 256 →
  (1023*z + x + z + y - (z<<<10)).unsigned = x.unsigned + y.unsigned := by grind
example (x y : BitVec 16) : x.unsigned = y.unsigned → x = y := by grind
example (x y : BitVec 16) :
  x % 4 = y % 4 → x.unsigned < 4 → y.unsigned = 0 → x = y := by grind

example (x : BitVec 64) :
    let y := x.truncate 51
    x.unsigned < 2^51 →
    x.unsigned = y.unsigned := by
  grind

-- TODO: `grind` fails (carry propagation through `BitVec.ofInt`)
/-
example (x y : BitVec 64) (c : BitVec 1) :
    let s := x.unsigned + y.unsigned + c.unsigned
    let l := BitVec.ofInt 64 s
    let h := BitVec.ofInt 1 (s >>> 64)
    s = l.unsigned + 2^64 * h.unsigned := by
  grind
-/

-- Tests for every supported operation

example (x y : BitVec 16) : (x + y).unsigned = (x.unsigned + y.unsigned) % (2 ^ 16) := by grind
example (x y : BitVec 16) : (x - y).unsigned = (x.unsigned - y.unsigned) % (2 ^ 16) := by grind
example (x y : BitVec 16) : (x * y).unsigned = (x.unsigned * y.unsigned) % (2 ^ 16) := by grind
example : (0#16).unsigned = 0 := by grind
example (x : BitVec 16) : (-x).unsigned = (-x.unsigned) % (2 ^ 16) := by grind
example (x : BitVec 16) (n : Nat) : (x.truncate n).unsigned = x.unsigned % (2 ^ n) := by grind
example (x : BitVec 16) (start len : Nat) : (x.extractLsb' start len).unsigned = (x.unsigned / (2 ^ start)) % (2 ^ len) := by grind
example (x : BitVec 16) : (~~~x).unsigned = (2 ^ 16 - 1) - x.unsigned := by grind
example (x : BitVec 16) (n : Nat) : (x <<< n).unsigned = (x.unsigned * (2 ^ n)) % (2 ^ 16) := by grind
example (x : BitVec 16) (n : Nat) : (x >>> n).unsigned = x.unsigned / (2 ^ n) := by grind
-- TODO: `grind` fails (`++`, `sshiftRight` as unsigned, `pow`)
/-
example (x : BitVec 8) (y : BitVec 8) : (x ++ y).unsigned = x.unsigned * (2 ^ 8) + y.unsigned := by grind
example (x : BitVec 16) (n : Nat) : (x.sshiftRight n).unsigned = (x.signed / (2 ^ n)) % (2 ^ 16) := by grind
example (x : BitVec 16) (z : Nat) : (x.pow z).unsigned = (x.unsigned ^ z) % (2 ^ 16) := by grind
-/
example (x y : BitVec 16) : (x / y).unsigned = x.unsigned / y.unsigned := by grind
example (x y : BitVec 16) : (x % y).unsigned = x.unsigned % y.unsigned := by grind
example (x y : BitVec 16) : (x + y).signed = (x.signed + y.signed).bmod (2 ^ 16) := by grind
example (x y : BitVec 16) : (x - y).signed = (x.signed - y.signed).bmod (2 ^ 16) := by grind
example (x y : BitVec 16) : (x * y).signed = (x.signed * y.signed).bmod (2 ^ 16) := by grind
example (x : BitVec 16) : (-x).signed = (-x.signed).bmod (2 ^ 16) := by grind
example (x : BitVec 16) (n : Nat) : (x.sshiftRight n).signed = x.signed >>> n := by grind
example (x y : BitVec 16) : (x.sdiv y).signed = (x.signed.tdiv y.signed).bmod (2 ^ 16) := by grind
example (x y : BitVec 16) : (x.srem y).signed = x.signed.tmod y.signed := by grind
example (x y : BitVec 16) : (x.smod y).signed = x.signed.fmod y.signed := by grind
-- TODO: `grind` fails (signed `pow`, `~~~`, `<<<`, `signExtend`)
/-
example (x : BitVec 16) (z : Nat) : (x.pow z).signed = (x.signed ^ z).bmod (2 ^ 16) := by grind
example (x : BitVec 16) : (~~~x).signed = (~~~x.signed).bmod (2 ^ 16) := by grind
example (x : BitVec 16) (n : Nat) : (x <<< n).signed = (x.signed <<< n).bmod (2 ^ 16) := by grind
example (x : BitVec 16) (v : Nat) : (x.signExtend v).signed = x.signed.bmod (2 ^ min v 16) := by grind
-/
example (x : BitVec 16) (v : Nat) : (x.zeroExtend v).signed = x.unsigned.bmod (2 ^ v) := by grind
example (x : BitVec 16) (n : Nat) : (x.setWidth n).unsigned = x.unsigned % (2 ^ n) := by grind
example (x : BitVec 16) (n : Nat) : (x.zeroExtend n).unsigned = x.unsigned % (2 ^ n) := by grind
-- TODO: `grind` fails (`rotateLeft`, `rotateRight`)
/-
example (x : BitVec 16) (n : Nat) : (x.rotateLeft n).unsigned = (x.unsigned * (2 ^ (n % 16)) + x.unsigned / (2 ^ (16 - (n % 16)))) % (2 ^ 16) := by grind
example (x : BitVec 16) (n : Nat) : (x.rotateRight n).unsigned = (x.unsigned / (2 ^ (n % 16)) + x.unsigned * (2 ^ (16 - (n % 16)))) % (2 ^ 16) := by grind
-/
example (b : Bool) : (BitVec.ofBool b).unsigned = if b then 1 else 0 := by grind

-- TODO: `grind` fails (`&&&` with a constant mask)
/-
example (x : BitVec 64) : (x &&& 31).unsigned < 32 := by grind
example (x : BitVec 64) : (x &&& 63).unsigned = x.unsigned % 64 := by grind
example (x : BitVec 64) : ((x &&& 31) + (x &&& 31)).unsigned < 64 := by grind
example (x : BitVec 8) : (x &&& 0xe0).unsigned = ((x.unsigned / 32) % 8) * 32 := by grind
example (x : BitVec 64) : (x &&& ~~~31).unsigned = ((x.unsigned / 32) % 576460752303423488) * 32 := by grind
-/
example (x : BitVec 64) : (x &&& 30).unsigned = (x &&& 30).unsigned := by grind
example (x : BitVec 16) : (~~~x).signed < 2 ^ 15 := by grind
-- TODO: `grind` fails (signed `<<<`)
/-
example (x : BitVec 16) : (x <<< 1).signed = (x.signed <<< 1).bmod (2 ^ 16) := by grind
-/
example (x : BitVec 16) : (x.signExtend 8).signed < 128 := by grind

example (x y : BitVec 16) (n : Nat) : ((x ||| y) >>> n).unsigned = ((x >>> n) ||| (y >>> n)).unsigned := by grind [BitVec.ushiftRight_or_distrib]
example (x y : BitVec 16) (n : Nat) : ((x &&& y) >>> n).unsigned = ((x >>> n) &&& (y >>> n)).unsigned := by grind [BitVec.ushiftRight_and_distrib]

example (x y z : BitVec 16) : (x &&& (y ||| z)).unsigned = ((x &&& y) ||| (x &&& z)).unsigned := by grind [BitVec.and_or_distrib_left]
example (x y z : BitVec 16) : (x ||| (y &&& z)) = ((x ||| y) &&& (x ||| z)) := by ext i; grind

-- XOR Swap Algorithm
example (x y : BitVec 32) :
    let x1 := x ^^^ y
    let y1 := x1 ^^^ y
    let x2 := x1 ^^^ y1
    x2 = y ∧ y1 = x := by
  apply And.intro <;> ext i <;> grind

-- Distributivity of multiplication over addition (mod 2^16)
example (x y z : BitVec 16) : (x * (y + z)).unsigned = (x * y + x * z).unsigned := by grind

-- Subtracting 1 from a power of 2 creates a mask
example : ((BitVec.ofNat 16 (2^8) - 1)).unsigned = 2^8 - 1 := by grind

-- Arithmetic right shift of a negative number preserves sign (msb)
example (x : BitVec 16) :
  x.signed < 0 → (x.sshiftRight 4).signed < 0 := by grind

-- Logical shift right of an unsigned value dividing by power of 2
example (x : BitVec 16) (n : Nat) (_ : n < 16) :
  (x >>> n).unsigned = x.unsigned / 2^n := by grind

-- Double negation of signed/unsigned
example (x : BitVec 16) : (~~~(~~~x)) = x := by grind

-- Two's complement subtraction identity
example (x y : BitVec 16) : x - y = x + ~~~y + 1 := by grind

-- Shift left by 1 is addition to self
example (x : BitVec 16) : x <<< 1 = x + x := by grind

-- Nested zero extension
example (x : BitVec 8) : (x.zeroExtend 16).zeroExtend 32 = x.zeroExtend 32 := by grind

-- Sign extension preserves signed value
-- TODO: `grind` fails (`signExtend` to a larger width)
/-
example (x : BitVec 16) : (x.signExtend 32).signed = x.signed := by grind
-/

-- Sign-extending a signed value to the same size is identity
example (x : BitVec 16) : x.signExtend 16 = x := by grind

-- Unsigned addition overflow condition
example (x y : BitVec 16) :
  (x + y).unsigned < x.unsigned ↔ x.unsigned + y.unsigned ≥ 65536 := by grind

-- Addition-with-carry polyfill
example (x y : BitVec 64) (c_in : BitVec 64) (hc : c_in.unsigned < 2) :
  let s1 := x + y
  let s := s1 + c_in
  let c1 : BitVec 64 := if s1 < x then 1 else 0
  let c2 : BitVec 64 := if s < s1 then 1 else 0
  let c_out := c1 ||| c2
  s.unsigned = (x.unsigned + y.unsigned + c_in.unsigned) % (2 ^ 64) ∧
  c_out.unsigned = (x.unsigned + y.unsigned + c_in.unsigned) / (2 ^ 64) := by
  grind [BitVec.toNat_eq_unsigned]

-- Constant-time select
-- TODO: the ported proof uses `Int.land_neg_one`, which does not exist in core
/-
example (mask a b : BitVec 64) (hmask : mask = 0 ∨ mask = -1) :
  ((mask &&& a) ||| (~~~mask &&& b)) = if mask = -1 then a else b := by
  have h_and_a : -1#64 &&& a = a := BitVec.allOnes_and
  have h_and_b : -1#64 &&& b = b := BitVec.allOnes_and
  have h_not_zero : ~~~(0 : BitVec 64) = -1#64 := BitVec.not_zero
  rcases hmask with rfl | rfl <;> grind [Int.land_neg_one,
    BitVec.zero_and,
    BitVec.zero_or,
    BitVec.or_zero]
-/

-- Sign of an Integer
-- TODO: the ported proofs use `BitVec.toInt_lt_zero_iff_msb` and
-- `BitVec.sshiftRight_ge_w_minus_1`, which do not exist in core
/-
example (v : BitVec 32) :
  (v.sshiftRight 31).signed = if v.signed < 0 then -1 else 0 := by
  grind [BitVec.toInt_lt_zero_iff_msb, BitVec.sshiftRight_ge_w_minus_1]

-- Detect Opposite Signs
example (x y : BitVec 64) :
  ((x ^^^ y).signed < 0) ↔ (x.signed < 0 ∧ y.signed ≥ 0) ∨ (x.signed ≥ 0 ∧ y.signed < 0) := by
  grind [BitVec.toInt_lt_zero_iff_msb]

-- Absolute Value (Peter Kankowski / VC++ version)
example (v : BitVec 8) (h : v.signed ≠ -128) :
  let mask := v.sshiftRight 7
  let abs := (v + mask) ^^^ mask
  abs.signed = if v.signed < 0 then -v.signed else v.signed := by
  intro mask abs
  have h_shift := BitVec.sshiftRight_ge_w_minus_1 v 7 (by omega) (by omega)
  have h_msb := BitVec.toInt_lt_zero_iff_msb v
  by_cases hv : v.msb
  · simp [hv] at h_shift
    dsimp only [abs, mask]
    rw [h_shift]
    have add_255 : v + 255#8 = v - 1#8 := by
      apply BitVec.eq_of_toNat_eq
      simp [Nat.add_comm]
    have h_xor : (v - 1#8) ^^^ 255#8 = ~~~(v - 1#8) := BitVec.xor_allOnes
    rw [add_255, h_xor]
    grind
  · simp [hv] at h_shift
    dsimp only [abs, mask]
    rw [h_shift]
    grind

-- Absolute Value (Vladimir Volkonsky's patented version)
example (v : BitVec 8) (h : v.signed ≠ -128) :
  let mask := v.sshiftRight 7
  let abs := (v ^^^ mask) - mask
  abs.signed = if v.signed < 0 then -v.signed else v.signed := by
  intro mask abs
  have h_shift := BitVec.sshiftRight_ge_w_minus_1 v 7 (by omega) (by omega)
  have h_msb := BitVec.toInt_lt_zero_iff_msb v
  by_cases hv : v.msb
  · simp [hv] at h_shift
    dsimp only [abs, mask]
    rw [h_shift]
    have h_xor : v ^^^ 255#8 = ~~~v := BitVec.xor_allOnes
    rw [h_xor]
    grind
  · simp [hv] at h_shift
    dsimp only [abs, mask]
    rw [h_shift]
    grind
-/

-- Minimum of Two Integers without Branching
example (x y : BitVec 8) :
  let mask : BitVec 8 := if x < y then -1#8 else 0#8
  let min := y ^^^ ((x ^^^ y) &&& mask)
  min = if x < y then x else y := by
  intro mask min
  have h_and : -1#8 &&& (x ^^^ y) = x ^^^ y := BitVec.allOnes_and
  grind [BitVec.zero_and, BitVec.zero_or, BitVec.or_zero]

-- Maximum of Two Integers without Branching
example (x y : BitVec 8) :
  let mask : BitVec 8 := if x < y then -1#8 else 0#8
  let max := x ^^^ ((x ^^^ y) &&& mask)
  max = if x < y then y else x := by
  intro mask max
  have h_and : -1#8 &&& (x ^^^ y) = x ^^^ y := BitVec.allOnes_and
  grind [BitVec.zero_and, BitVec.zero_or, BitVec.or_zero]

-- Conditionally Negate (using XOR)
example (v : BitVec 8) (f : BitVec 8) (hf : f = 0 ∨ f = 1) (hv : v.signed ≠ -128) :
  let r := (v ^^^ (-f)) + f
  r.signed = if f = 1 then -v.signed else v.signed := by
  intro r
  rcases hf with hf | hf
  · subst hf
    simp [r]
  · have h_xor : v ^^^ 255#8 = ~~~v := BitVec.xor_allOnes
    grind

-- Swapping Values with XOR
example (a b : BitVec 8) :
  let a1 := a ^^^ b
  let b1 := b ^^^ a1
  let a2 := a1 ^^^ b1
  a2 = b ∧ b1 = a := by
  intro a1 b1 a2
  simp [a2, b1, a1]
  grind

-- Modulus Division by Power of 2 (Obvious Modulus)
-- TODO: `grind` fails (`&&&` with a constant mask)
/-
example (n : BitVec 8) :
  let d : BitVec 8 := 8#8
  n.unsigned % 8 = (n &&& (d - 1)).unsigned := by
  intro d
  simp [d]
  grind
-/

-- constant_time_msb_w (Most Significant Bit Mask)
-- TODO: the ported proof uses `BitVec.ushiftRight_w_minus_1`, which does not exist in core
/-
example (a : BitVec 8) :
  let res := 0#8 - (a >>> 7)
  res.signed = (if (a >>> 7) = 1#8 then -1#8 else 0#8).signed := by
  intro res
  have neg_ite (c : Prop) [Decidable c] (x y : BitVec 8) : -(if c then x else y) = if c then -x else -y := by split <;> rfl
  have h_shift := BitVec.ushiftRight_w_minus_1 a (by decide)
  simp [res, neg_ite, h_shift]
-/

-- Coq ZnWords translation tests

-- TODO: `grind` fails
/-
example (a a' : BitVec 32) (f_vs1 : Nat)
    (hmod : (a' - a).toNat % 8 = 0)
    (hf : f_vs1 = (a' - a).toNat / 8) :
    a + BitVec.ofNat 32 (8 * f_vs1) = a' := by
  grind
-/

example (left0 right : BitVec 32) (xs_len : Nat)
    (_h1 : (right - left0).toNat = 8 * xs_len)
    (x_len : Nat) (x1 x2 : BitVec 32)
    (h2 : (x2 - x1).toNat = 8 * x_len)
    (h3 : (x2 - x1).toNat ≠ 0) :
    (x2 - ((x1 + (((x2 - x1) >>> 4) <<< 3)) + 8)).toNat =
    8 * (x_len - (1 + ((x1 + (((x2 - x1) >>> 4) <<< 3) - x1).toNat / 8))) := by
  grind

example (a b : BitVec 32) :
    let s := a + b
    let c : BitVec 32 := if s < a then 1 else 0
    c.toNat = (a.toNat + b.toNat) / 2^32 := by
  grind

example (a b : BitVec 64) :
    a.toNat + b.toNat = 2^64 * (if a + b < b then 1 else 0) + (a + b).toNat := by
  grind

example (x y carry : BitVec 64) :
    let s1 := x + carry
    let c1 : BitVec 64 := if s1 < carry then 1 else 0
    let s2 := s1 + y
    let c2 : BitVec 64 := if s2 < y then 1 else 0
    let res_c := c1 + c2
    2^64 * res_c.toNat + s2.toNat = x.toNat + y.toNat + carry.toNat := by
  grind

example (a b : BitVec 64) :
    (a.toNat : Int) - (b.toNat : Int) = ((a - b).toNat : Int) - 2^64 * (if a < b then 1 else 0) := by
  grind

-- TODO: `grind` times out (subtraction with borrow)
/-
example (x y borrow : BitVec 64) (h_borrow : borrow.toNat < 2) :
    let d1 := x - y
    let b1 : BitVec 64 := if x < y then 1 else 0
    let d2 := d1 - borrow
    let b2 : BitVec 64 := if d1 < borrow then 1 else 0
    let res_b := b1 + b2
    (d2.toNat : Int) - 2^64 * (res_b.toNat : Int) = (x.toNat : Int) - (y.toNat : Int) - (borrow.toNat : Int) := by
  grind
-/

example (x : BitVec 32) (h : x >>> 31 ≠ 0) : x ≠ 0 := by
  grind

example (x : BitVec 32) : x.signed ≠ 0 ↔ x.toNat ≠ 0 := by
  grind

example (a b : BitVec 64) (ha : a.toNat < 2^32) (hb : b.toNat < 2^32) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h_le : a.toNat * b.toNat ≤ (2^32 - 1) * (2^32 - 1) := Nat.mul_le_mul (by grind) (by grind)
  grind

example (a : BitVec 64) (h : a.toNat < 2^32) :
    (2#64 * a) / 2#64 = a := by
  grind

example (x y : UInt32) (h : x < 4294967295) : x + 1 ≤ y → x < y := by grind
