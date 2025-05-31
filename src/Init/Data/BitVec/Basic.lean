/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Leonardo de Moura, Mario Carneiro, Alex Keizer, Harun Khan, Abdalrhman M Mohamed, Siddharth Bhat
-/
module

prelude
import Init.Data.Fin.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Power2
import Init.Data.Int.Bitwise
import Init.Data.BitVec.BasicAux

/-!
We define the basic algebraic structure of bitvectors. We choose the `Fin` representation over
others for its relative efficiency (Lean has special support for `Nat`),  and the fact that bitwise
operations on `Fin` are already defined. Some other possible representations are `List Bool`,
`{ l : List Bool // l.length = w }`, `Fin w → Bool`.

We define many of the bitvector operations from the
[`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV).
of SMT-LIB v2.
-/

set_option linter.missingDocs true

namespace BitVec

@[inline, deprecated BitVec.ofNatLT (since := "2025-02-13"), inherit_doc BitVec.ofNatLT]
protected def ofNatLt {n : Nat} (i : Nat) (p : i < 2 ^ n) : BitVec n :=
  BitVec.ofNatLT i p

section Nat

instance natCastInst : NatCast (BitVec w) := ⟨BitVec.ofNat w⟩

/-- Theorem for normalizing the bitvector literal representation. -/
-- TODO: This needs more usage data to assess which direction the simp should go.
@[simp, bitvec_to_nat] theorem ofNat_eq_ofNat : @OfNat.ofNat (BitVec n) i _ = .ofNat n i := rfl

-- Note. Mathlib would like this to go the other direction.
@[simp] theorem natCast_eq_ofNat (w x : Nat) : @Nat.cast (BitVec w) _ x = .ofNat w x := rfl

end Nat

section subsingleton

/-- All empty bitvectors are equal -/
instance : Subsingleton (BitVec 0) where
  allEq := by intro ⟨0, _⟩ ⟨0, _⟩; rfl

/-- The empty bitvector. -/
abbrev nil : BitVec 0 := 0

/-- Every bitvector of length 0 is equal to `nil`, i.e., there is only one empty bitvector -/
theorem eq_nil (x : BitVec 0) : x = nil := Subsingleton.allEq ..

end subsingleton

section zero_allOnes

/-- Returns a bitvector of size `n` where all bits are `0`. -/
@[expose] protected def zero (n : Nat) : BitVec n := .ofNatLT 0 (Nat.two_pow_pos n)
instance : Inhabited (BitVec n) where default := .zero n

/-- Returns a bitvector of size `n` where all bits are `1`. -/
def allOnes (n : Nat) : BitVec n :=
  .ofNatLT (2^n - 1) (Nat.le_of_eq (Nat.sub_add_cancel (Nat.two_pow_pos n)))

end zero_allOnes

section getXsb

/--
Returns the `i`th least significant bit.

This will be renamed `getLsb` after the existing deprecated alias is removed.
-/
@[inline, expose] def getLsb' (x : BitVec w) (i : Fin w) : Bool := x.toNat.testBit i

/-- Returns the `i`th least significant bit, or `none` if `i ≥ w`. -/
@[inline, expose] def getLsb? (x : BitVec w) (i : Nat) : Option Bool :=
  if h : i < w then some (getLsb' x ⟨i, h⟩) else none

/--
Returns the `i`th most significant bit.

This will be renamed `BitVec.getMsb` after the existing deprecated alias is removed.
-/
@[inline] def getMsb' (x : BitVec w) (i : Fin w) : Bool := x.getLsb' ⟨w-1-i, by omega⟩

/-- Returns the `i`th most significant bit or `none` if `i ≥ w`. -/
@[inline] def getMsb? (x : BitVec w) (i : Nat) : Option Bool :=
  if h : i < w then some (getMsb' x ⟨i, h⟩) else none

/-- Returns the `i`th least significant bit or `false` if `i ≥ w`. -/
@[inline, expose] def getLsbD (x : BitVec w) (i : Nat) : Bool :=
  x.toNat.testBit i

/-- Returns the `i`th most significant bit, or `false` if `i ≥ w`. -/
@[inline] def getMsbD (x : BitVec w) (i : Nat) : Bool :=
  i < w && x.getLsbD (w-1-i)

/-- Returns the most significant bit in a bitvector. -/
@[inline] protected def msb (x : BitVec n) : Bool := getMsbD x 0

end getXsb

section getElem

instance : GetElem (BitVec w) Nat Bool fun _ i => i < w where
  getElem xs i h := xs.getLsb' ⟨i, h⟩

/-- We prefer `x[i]` as the simp normal form for `getLsb'` -/
@[simp] theorem getLsb'_eq_getElem (x : BitVec w) (i : Fin w) :
    x.getLsb' i = x[i] := rfl

/-- We prefer `x[i]?` as the simp normal form for `getLsb?` -/
@[simp] theorem getLsb?_eq_getElem? (x : BitVec w) (i : Nat) :
    x.getLsb? i = x[i]? := rfl

theorem getElem_eq_testBit_toNat (x : BitVec w) (i : Nat) (h : i < w) :
  x[i] = x.toNat.testBit i := rfl

@[simp]
theorem getLsbD_eq_getElem {x : BitVec w} {i : Nat} (h : i < w) :
    x.getLsbD i = x[i] := rfl

end getElem

section Int

/--
Interprets the bitvector as an integer stored in two's complement form.
-/
@[expose]
protected def toInt (x : BitVec n) : Int :=
  if 2 * x.toNat < 2^n then
    x.toNat
  else
    (x.toNat : Int) - (2^n : Nat)

/--
Converts an integer to its two's complement representation as a bitvector of the given width `n`,
over- and underflowing as needed.

The underlying `Nat` is `(2^n + (i mod 2^n)) mod 2^n`. Converting the bitvector back to an `Int`
with `BitVec.toInt` results in the value `i.bmod (2^n)`.
-/
@[expose]
protected def ofInt (n : Nat) (i : Int) : BitVec n := .ofNatLT (i % (Int.ofNat (2^n))).toNat (by
  apply (Int.toNat_lt _).mpr
  · apply Int.emod_lt_of_pos
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  · apply Int.emod_nonneg
    intro eq
    apply Nat.ne_of_gt (Nat.two_pow_pos n)
    exact Int.ofNat_inj.mp eq)

instance : IntCast (BitVec w) := ⟨BitVec.ofInt w⟩

end Int

section Syntax

/-- Notation for bitvector literals. `i#n` is a shorthand for `BitVec.ofNat n i`. -/
syntax:max num noWs "#" noWs term:max : term
macro_rules | `($i:num#$n) => `(BitVec.ofNat $n $i)

/-- not `ofNat_zero` -/
recommended_spelling "zero" for "0#n" in [BitVec.ofNat, «term__#__»]
/-- not `ofNat_one` -/
recommended_spelling "one" for "1#n" in [BitVec.ofNat, «term__#__»]

/-- Unexpander for bitvector literals. -/
@[app_unexpander BitVec.ofNat] def unexpandBitVecOfNat : Lean.PrettyPrinter.Unexpander
  | `($(_) $n $i:num) => `($i:num#$n)
  | _ => throw ()

/-- Notation for bitvector literals without truncation. `i#'lt` is a shorthand for `BitVec.ofNatLT i lt`. -/
scoped syntax:max term:max noWs "#'" noWs term:max : term
macro_rules | `($i#'$p) => `(BitVec.ofNatLT $i $p)

/-- Unexpander for bitvector literals without truncation. -/
@[app_unexpander BitVec.ofNatLT] def unexpandBitVecOfNatLt : Lean.PrettyPrinter.Unexpander
  | `($(_) $i $p) => `($i#'$p)
  | _ => throw ()

end Syntax

section repr_toString

/--
Converts a bitvector into a fixed-width hexadecimal number with enough digits to represent it.

If `n` is `0`, then one digit is returned. Otherwise, `⌊(n + 3) / 4⌋` digits are returned.
-/
protected def toHex {n : Nat} (x : BitVec n) : String :=
  let s := (Nat.toDigits 16 x.toNat).asString
  let t := (List.replicate ((n+3) / 4 - s.length) '0').asString
  t ++ s

/-- `BitVec` representation. -/
protected def BitVec.repr (a : BitVec n) : Std.Format :=
  "0x" ++ (a.toHex : Std.Format) ++ "#" ++ repr n

instance : Repr (BitVec n) where
  reprPrec a _ := BitVec.repr a

instance : ToString (BitVec n) where toString a := toString (repr a)

end repr_toString

section arithmetic

/--
Negation of bitvectors. This can be interpreted as either signed or unsigned negation modulo `2^n`.
Usually accessed via the `-` prefix operator.

SMT-LIB name: `bvneg`.
-/
@[expose]
protected def neg (x : BitVec n) : BitVec n := .ofNat n (2^n - x.toNat)
instance : Neg (BitVec n) := ⟨.neg⟩

/--
Returns the absolute value of a signed bitvector.
-/
@[expose]
protected def abs (x : BitVec n) : BitVec n := if x.msb then .neg x else x

/--
Multiplies two bitvectors. This can be interpreted as either signed or unsigned multiplication
modulo `2^n`. Usually accessed via the `*` operator.

SMT-LIB name: `bvmul`.
-/
@[expose]
protected def mul (x y : BitVec n) : BitVec n := BitVec.ofNat n (x.toNat * y.toNat)
instance : Mul (BitVec n) := ⟨.mul⟩

/--
Raises a bitvector to a natural number power. Usually accessed via the `^` operator.

Note that this is currently an inefficient implementation,
and should be replaced via an `@[extern]` with a native implementation.
See https://github.com/leanprover/lean4/issues/7887.
-/
@[expose]
protected def pow (x : BitVec n) (y : Nat) : BitVec n :=
  match y with
  | 0 => 1
  | y + 1 => x.pow y * x
instance : Pow (BitVec n) Nat where
  pow x y := x.pow y

/--
Unsigned division of bitvectors using the Lean convention where division by zero returns zero.
Usually accessed via the `/` operator.
-/
@[expose]
def udiv (x y : BitVec n) : BitVec n :=
  (x.toNat / y.toNat)#'(Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)
instance : Div (BitVec n) := ⟨.udiv⟩

/--
Unsigned modulo for bitvectors. Usually accessed via the `%` operator.

SMT-LIB name: `bvurem`.
-/
@[expose]
def umod (x y : BitVec n) : BitVec n :=
  (x.toNat % y.toNat)#'(Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)
instance : Mod (BitVec n) := ⟨.umod⟩

/--
Unsigned division of bitvectors using the
[SMT-LIB convention](http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml),
where division by zero returns `BitVector.allOnes n`.

SMT-LIB name: `bvudiv`.
-/
@[expose]
def smtUDiv (x y : BitVec n) : BitVec n := if y = 0 then allOnes n else udiv x y

/--
Signed T-division (using the truncating rounding convention) for bitvectors. This function obeys the
Lean convention that division by zero returns zero.

Examples:
* `(7#4).sdiv 2 = 3#4`
* `(-9#4).sdiv 2 = -4#4`
* `(5#4).sdiv -2 = -2#4`
* `(-7#4).sdiv (-2) = 3#4`
-/
def sdiv (x y : BitVec n) : BitVec n :=
  match x.msb, y.msb with
  | false, false => udiv x y
  | false, true  => .neg (udiv x (.neg y))
  | true,  false => .neg (udiv (.neg x) y)
  | true,  true  => udiv (.neg x) (.neg y)

/--
Signed division for bitvectors using the SMT-LIB using the
[SMT-LIB convention](http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml),
where division by zero returns `BitVector.allOnes n`.

Specifically, `x.smtSDiv 0 = if x >= 0 then -1 else 1`

SMT-LIB name: `bvsdiv`.
-/
def smtSDiv (x y : BitVec n) : BitVec n :=
  match x.msb, y.msb with
  | false, false => smtUDiv x y
  | false, true  => .neg (smtUDiv x (.neg y))
  | true,  false => .neg (smtUDiv (.neg x) y)
  | true,  true  => smtUDiv (.neg x) (.neg y)

/--
Remainder for signed division rounding to zero.

SMT-LIB name: `bvsrem`.
-/
def srem (x y : BitVec n) : BitVec n :=
  match x.msb, y.msb with
  | false, false => umod x y
  | false, true  => umod x (.neg y)
  | true,  false => .neg (umod (.neg x) y)
  | true,  true  => .neg (umod (.neg x) (.neg y))

/--
Remainder for signed division rounded to negative infinity.

SMT-LIB name: `bvsmod`.
-/
def smod (x y : BitVec m) : BitVec m :=
  match x.msb, y.msb with
  | false, false => umod x y
  | false, true =>
    let u := umod x (.neg y)
    (if u = .zero m then u else .add u y)
  | true, false =>
    let u := umod (.neg x) y
    (if u = .zero m then u else .sub y u)
  | true, true => .neg (umod (.neg x) (.neg y))

end arithmetic


section bool

/-- Turns a `Bool` into a bitvector of length `1`. -/
@[expose]
def ofBool (b : Bool) : BitVec 1 := cond b 1 0

@[simp] theorem ofBool_false : ofBool false = 0 := by trivial
@[simp] theorem ofBool_true  : ofBool true  = 1 := by trivial

/-- Fills a bitvector with `w` copies of the bit `b`. -/
def fill (w : Nat) (b : Bool) : BitVec w := bif b then -1 else 0

end bool

section relations

/--
Unsigned less-than for bitvectors.

SMT-LIB name: `bvult`.
-/
@[expose]
protected def ult (x y : BitVec n) : Bool := x.toNat < y.toNat

/--
Unsigned less-than-or-equal-to for bitvectors.

SMT-LIB name: `bvule`.
-/
@[expose]
protected def ule (x y : BitVec n) : Bool := x.toNat ≤ y.toNat

/--
Signed less-than for bitvectors.

SMT-LIB name: `bvslt`.

Examples:
 * `BitVec.slt 6#4 7 = true`
 * `BitVec.slt 7#4 8 = false`
-/
@[expose]
protected def slt (x y : BitVec n) : Bool := x.toInt < y.toInt

/--
Signed less-than-or-equal-to for bitvectors.

SMT-LIB name: `bvsle`.
-/
@[expose]
protected def sle (x y : BitVec n) : Bool := x.toInt ≤ y.toInt

end relations

section cast

/--
If two natural numbers `n` and `m` are equal, then a bitvector of width `n` is also a bitvector of
width `m`.

Using `x.cast eq` should be preferred over `eq ▸ x` because there are special-purpose `simp` lemmas
that can more consistently simplify `BitVec.cast` away.
-/
@[inline, expose] protected def cast (eq : n = m) (x : BitVec n) : BitVec m := .ofNatLT x.toNat (eq ▸ x.isLt)

@[simp] theorem cast_ofNat {n m : Nat} (h : n = m) (x : Nat) :
    (BitVec.ofNat n x).cast h = BitVec.ofNat m x := by
  subst h; rfl

@[simp] theorem cast_cast {n m k : Nat} (h₁ : n = m) (h₂ : m = k) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x.cast (h₁ ▸ h₂) :=
  rfl

@[simp] theorem cast_eq {n : Nat} (h : n = n) (x : BitVec n) : x.cast h = x := rfl

/--
Extracts the bits `start` to `start + len - 1` from a bitvector of size `n` to yield a
new bitvector of size `len`. If `start + len > n`, then the bitvector is zero-extended.
-/
@[expose]
def extractLsb' (start len : Nat) (x : BitVec n) : BitVec len := .ofNat _ (x.toNat >>> start)

/--
Extracts the bits from `hi` down to `lo` (both inclusive) from a bitvector, which is implicitly
zero-extended if necessary.

The resulting bitvector has size `hi - lo + 1`.

SMT-LIB name: `extract`.
-/
@[expose]
def extractLsb (hi lo : Nat) (x : BitVec n) : BitVec (hi - lo + 1) := extractLsb' lo _ x

/--
Increases the width of a bitvector to one that is at least as large by zero-extending it.

This is a constant-time operation because the underlying `Nat` is unmodified; because the new width
is at least as large as the old one, no overflow is possible.
-/
@[expose]
def setWidth' {n w : Nat} (le : n ≤ w) (x : BitVec n) : BitVec w :=
  x.toNat#'(by
    apply Nat.lt_of_lt_of_le x.isLt
    exact Nat.pow_le_pow_right (by trivial) le)

/--
Returns `zeroExtend (w+n) x <<< n` without needing to compute `x % 2^(2+n)`.
-/
@[expose]
def shiftLeftZeroExtend (msbs : BitVec w) (m : Nat) : BitVec (w + m) :=
  let shiftLeftLt {x : Nat} (p : x < 2^w) (m : Nat) : x <<< m < 2^(w + m) := by
        simp [Nat.shiftLeft_eq, Nat.pow_add]
        apply Nat.mul_lt_mul_of_pos_right p
        exact (Nat.two_pow_pos m)
  (msbs.toNat <<< m)#'(shiftLeftLt msbs.isLt m)


/--
Transforms a bitvector of length `w` into a bitvector of length `v`, padding with `0` as needed.

The specific behavior depends on the relationship between the starting width `w` and the final width
`v`:
 * If `v > w`, it is zero-extended; the high bits are padded with zeroes until the bitvector has `v`
   bits.
 * If `v = w`, the bitvector is returned unchanged.
 * If `v < w`, the high bits are truncated.

`BitVec.setWidth`, `BitVec.zeroExtend`, and `BitVec.truncate` are aliases for this operation.

SMT-LIB name: `zero_extend`.
-/
def setWidth (v : Nat) (x : BitVec w) : BitVec v :=
  if h : w ≤ v then
    setWidth' h x
  else
    .ofNat v x.toNat

@[inherit_doc setWidth]
abbrev zeroExtend := @setWidth

@[inherit_doc setWidth]
abbrev truncate := @setWidth

/--
Transforms a bitvector of length `w` into a bitvector of length `v`, padding as needed with the most
significant bit's value.

If `x` is an empty bitvector, then the sign is treated as zero.

SMT-LIB name: `sign_extend`.
-/
def signExtend (v : Nat) (x : BitVec w) : BitVec v := .ofInt v x.toInt

end cast

section bitwise

/--
Bitwise and for bitvectors. Usually accessed via the `&&&` operator.

SMT-LIB name: `bvand`.

Example:
 * `0b1010#4 &&& 0b0110#4 = 0b0010#4`
-/
@[expose]
protected def and (x y : BitVec n) : BitVec n :=
  (x.toNat &&& y.toNat)#'(Nat.and_lt_two_pow x.toNat y.isLt)
instance : AndOp (BitVec w) := ⟨.and⟩

/--
Bitwise or for bitvectors. Usually accessed via the `|||` operator.

SMT-LIB name: `bvor`.

Example:
 * `0b1010#4 ||| 0b0110#4 = 0b1110#4`
-/
@[expose]
protected def or (x y : BitVec n) : BitVec n :=
  (x.toNat ||| y.toNat)#'(Nat.or_lt_two_pow x.isLt y.isLt)
instance : OrOp (BitVec w) := ⟨.or⟩

/--
Bitwise xor for bitvectors. Usually accessed via the `^^^` operator.

SMT-LIB name: `bvxor`.

Example:
 * `0b1010#4 ^^^ 0b0110#4 = 0b1100#4`
-/
@[expose]
protected def xor (x y : BitVec n) : BitVec n :=
  (x.toNat ^^^ y.toNat)#'(Nat.xor_lt_two_pow x.isLt y.isLt)
instance : Xor (BitVec w) := ⟨.xor⟩

/--
Bitwise complement for bitvectors. Usually accessed via the `~~~` prefix operator.

SMT-LIB name: `bvnot`.

Example:
 * `~~~(0b0101#4) == 0b1010`
-/
@[expose]
protected def not (x : BitVec n) : BitVec n := allOnes n ^^^ x
instance : Complement (BitVec w) := ⟨.not⟩

/--
Shifts a bitvector to the left. The low bits are filled with zeros. As a numeric operation, this is
equivalent to `x * 2^s`, modulo `2^n`.

SMT-LIB name: `bvshl` except this operator uses a `Nat` shift value.
-/
@[expose]
protected def shiftLeft (x : BitVec n) (s : Nat) : BitVec n := BitVec.ofNat n (x.toNat <<< s)
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨.shiftLeft⟩

/--
Shifts a bitvector to the right. This is a logical right shift - the high bits are filled with
zeros.

As a numeric operation, this is equivalent to `x / 2^s`, rounding down.

SMT-LIB name: `bvlshr` except this operator uses a `Nat` shift value.
-/
@[expose]
def ushiftRight (x : BitVec n) (s : Nat) : BitVec n :=
  (x.toNat >>> s)#'(by
  let ⟨x, lt⟩ := x
  simp only [BitVec.toNat, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)]
  rw [←Nat.mul_one x]
  exact Nat.mul_lt_mul_of_lt_of_le' lt (Nat.two_pow_pos s) (Nat.le_refl 1))

instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨.ushiftRight⟩

/--
Shifts a bitvector to the right. This is an arithmetic right shift - the high bits are filled with
most significant bit's value.

As a numeric operation, this is equivalent to `x.toInt >>> s`.

SMT-LIB name: `bvashr` except this operator uses a `Nat` shift value.
-/
@[expose]
def sshiftRight (x : BitVec n) (s : Nat) : BitVec n := .ofInt n (x.toInt >>> s)

instance {n} : HShiftLeft  (BitVec m) (BitVec n) (BitVec m) := ⟨fun x y => x <<< y.toNat⟩
instance {n} : HShiftRight (BitVec m) (BitVec n) (BitVec m) := ⟨fun x y => x >>> y.toNat⟩

/--
Shifts a bitvector to the right. This is an arithmetic right shift - the high bits are filled with
most significant bit's value.

As a numeric operation, this is equivalent to `a.toInt >>> s.toNat`.

SMT-LIB name: `bvashr`.
-/
@[expose]
def sshiftRight' (a : BitVec n) (s : BitVec m) : BitVec n := a.sshiftRight s.toNat

/-- Auxiliary function for `rotateLeft`, which does not take into account the case where
the rotation amount is greater than the bitvector width. -/
@[expose]
def rotateLeftAux (x : BitVec w) (n : Nat) : BitVec w :=
  x <<< n ||| x >>> (w - n)

/--
Rotates the bits in a bitvector to the left.

All the bits of `x` are shifted to higher positions, with the top `n` bits wrapping around to fill
the vacated low bits.

SMT-LIB name: `rotate_left`, except this operator uses a `Nat` shift amount.

Example:
 * `(0b0011#4).rotateLeft 3 = 0b1001`
-/
@[expose]
def rotateLeft (x : BitVec w) (n : Nat) : BitVec w := rotateLeftAux x (n % w)


/--
Auxiliary function for `rotateRight`, which does not take into account the case where
the rotation amount is greater than the bitvector width.
-/
@[expose]
def rotateRightAux (x : BitVec w) (n : Nat) : BitVec w :=
  x >>> n ||| x <<< (w - n)

/--
Rotates the bits in a bitvector to the right.

All the bits of `x` are shifted to lower positions, with the bottom `n` bits wrapping around to fill
the vacated high bits.

SMT-LIB name: `rotate_right`, except this operator uses a `Nat` shift amount.

Example:
 * `rotateRight 0b01001#5 1 = 0b10100`
-/
@[expose]
def rotateRight (x : BitVec w) (n : Nat) : BitVec w := rotateRightAux x (n % w)

/--
Concatenates two bitvectors using the “big-endian” convention that the more significant
input is on the left. Usually accessed via the `++` operator.

SMT-LIB name: `concat`.

Example:
 * `0xAB#8 ++ 0xCD#8 = 0xABCD#16`.
-/
@[expose]
def append (msbs : BitVec n) (lsbs : BitVec m) : BitVec (n+m) :=
  shiftLeftZeroExtend msbs m ||| setWidth' (Nat.le_add_left m n) lsbs

instance : HAppend (BitVec w) (BitVec v) (BitVec (w + v)) := ⟨.append⟩

-- TODO: write this using multiplication
/-- Concatenates `i` copies of `x` into a new vector of length `w * i`. -/
def replicate : (i : Nat) → BitVec w → BitVec (w*i)
  | 0,   _ => 0#0
  | n+1, x =>
    (x ++ replicate n x).cast (by rw [Nat.mul_succ]; omega)

/-!
### Cons and Concat
We give special names to the operations of adding a single bit to either end of a bitvector.
We follow the precedent of `Vector.cons`/`Vector.concat` both for the name, and for the decision
to have the resulting size be `n + 1` for both operations (rather than `1 + n`, which would be the
result of appending a single bit to the front in the naive implementation).
-/

/-- Append a single bit to the end of a bitvector, using big endian order (see `append`).
    That is, the new bit is the least significant bit. -/
@[expose]
def concat {n} (msbs : BitVec n) (lsb : Bool) : BitVec (n+1) := msbs ++ (ofBool lsb)

/--
Shifts all bits of `x` to the left by `1` and sets the least significant bit to `b`.

This is a non-dependent version of `BitVec.concat` that does not change the total bitwidth.
-/
@[expose]
def shiftConcat (x : BitVec n) (b : Bool) : BitVec n :=
  (x.concat b).truncate n

/--
Prepends a single bit to the front of a bitvector, using big-endian order (see `append`).

The new bit is the most significant bit.
-/
@[expose]
def cons {n} (msb : Bool) (lsbs : BitVec n) : BitVec (n+1) :=
  ((ofBool msb) ++ lsbs).cast (Nat.add_comm ..)

theorem append_ofBool (msbs : BitVec w) (lsb : Bool) :
    msbs ++ ofBool lsb = concat msbs lsb :=
  rfl

theorem ofBool_append (msb : Bool) (lsbs : BitVec w) :
    ofBool msb ++ lsbs = (cons msb lsbs).cast (Nat.add_comm ..) :=
  rfl

/--
`twoPow w i` is the bitvector `2^i` if `i < w`, and `0` otherwise. In other words, it is 2 to the
power `i`.

From the bitwise point of view, it has the `i`th bit as `1` and all other bits as `0`.
-/
def twoPow (w : Nat) (i : Nat) : BitVec w := 1#w <<< i

end bitwise

/--
Computes a hash of a bitvector, combining 64-bit words using `mixHash`.
-/
def hash (bv : BitVec n) : UInt64 :=
  if n ≤ 64 then
    bv.toFin.val.toUInt64
  else
    mixHash (bv.toFin.val.toUInt64) (hash ((bv >>> 64).setWidth (n - 64)))

instance : Hashable (BitVec n) where
  hash := hash

section normalization_eqs
/-! We add simp-lemmas that rewrite bitvector operations into the equivalent notation -/
@[simp] theorem append_eq (x : BitVec w) (y : BitVec v)   : BitVec.append x y = x ++ y        := rfl
@[simp] theorem shiftLeft_eq (x : BitVec w) (n : Nat)     : BitVec.shiftLeft x n = x <<< n    := rfl
@[simp] theorem ushiftRight_eq (x : BitVec w) (n : Nat)   : BitVec.ushiftRight x n = x >>> n  := rfl
@[simp] theorem not_eq (x : BitVec w)                     : BitVec.not x = ~~~x               := rfl
@[simp] theorem and_eq (x y : BitVec w)                   : BitVec.and x y = x &&& y          := rfl
@[simp] theorem or_eq (x y : BitVec w)                    : BitVec.or x y = x ||| y           := rfl
@[simp] theorem xor_eq (x y : BitVec w)                   : BitVec.xor x y = x ^^^ y          := rfl
@[simp] theorem neg_eq (x : BitVec w)                     : BitVec.neg x = -x                 := rfl
@[simp] theorem add_eq (x y : BitVec w)                   : BitVec.add x y = x + y            := rfl
@[simp] theorem sub_eq (x y : BitVec w)                   : BitVec.sub x y = x - y            := rfl
@[simp] theorem mul_eq (x y : BitVec w)                   : BitVec.mul x y = x * y            := rfl
@[simp] theorem udiv_eq (x y : BitVec w)                  : BitVec.udiv x y = x / y           := rfl
@[simp] theorem umod_eq (x y : BitVec w)                  : BitVec.umod x y = x % y           := rfl
@[simp] theorem zero_eq                                   : BitVec.zero n = 0#n               := rfl
end normalization_eqs

/-- Converts a list of `Bool`s into a big-endian `BitVec`. -/
def ofBoolListBE : (bs : List Bool) → BitVec bs.length
| [] => 0#0
| b :: bs => cons b (ofBoolListBE bs)

/-- Converts a list of `Bool`s into a little-endian `BitVec`. -/
def ofBoolListLE : (bs : List Bool) → BitVec bs.length
| [] => 0#0
| b :: bs => concat (ofBoolListLE bs) b

/-! ## Overflow -/

/--
Checks whether addition of `x` and `y` results in *unsigned* overflow.

SMT-LIB name: `bvuaddo`.
-/
def uaddOverflow {w : Nat} (x y : BitVec w) : Bool := x.toNat + y.toNat ≥ 2 ^ w

/--
Checks whether addition of `x` and `y` results in *signed* overflow, treating `x` and `y` as 2's
complement signed bitvectors.

SMT-LIB name: `bvsaddo`.
-/
def saddOverflow {w : Nat} (x y : BitVec w) : Bool :=
  (x.toInt + y.toInt ≥ 2 ^ (w - 1)) || (x.toInt + y.toInt < - 2 ^ (w - 1))

/--
Checks whether subtraction of `x` and `y` results in *unsigned* overflow.

SMT-Lib name: `bvusubo`.
-/
@[expose]
def usubOverflow {w : Nat} (x y : BitVec w) : Bool := x.toNat < y.toNat

/--
Checks whether the subtraction of `x` and `y` results in *signed* overflow, treating `x` and `y` as
2's complement signed bitvectors.

SMT-Lib name: `bvssubo`.
-/
@[expose]
def ssubOverflow {w : Nat} (x y : BitVec w) : Bool :=
  (x.toInt - y.toInt ≥ 2 ^ (w - 1)) || (x.toInt - y.toInt < - 2 ^ (w - 1))

/--
Checks whether the negation of a bitvector results in overflow.

For a bitvector `x` with nonzero width, this only happens if `x = intMin`.

SMT-Lib name: `bvnego`.
-/
@[expose]
def negOverflow {w : Nat} (x : BitVec w) : Bool :=
  x.toInt == - 2 ^ (w - 1)

/--
Checks whether the signed division of `x` by `y` results in overflow.
For BitVecs `x` and `y` with nonzero width, this only happens if `x = intMin` and `y = allOnes w`.

SMT-LIB name: `bvsdivo`.
-/
@[expose]
def sdivOverflow {w : Nat} (x y : BitVec w) : Bool :=
  (2 ^ (w - 1) ≤ x.toInt / y.toInt) || (x.toInt / y.toInt <  - 2 ^ (w - 1))

/- ### reverse -/

/-- Reverses the bits in a bitvector. -/
def reverse : {w : Nat} → BitVec w → BitVec w
  | 0, x => x
  | w + 1, x => concat (reverse (x.truncate w)) (x.msb)

/--  `umulOverflow x y` returns `true` if multiplying `x` and `y` results in *unsigned* overflow.

  SMT-Lib name: `bvumulo`.
-/
def umulOverflow {w : Nat} (x y : BitVec w) : Bool := x.toNat * y.toNat ≥ 2 ^ w

/-- `smulOverflow x y` returns `true` if multiplying `x` and `y` results in *signed* overflow,
treating `x` and `y` as 2's complement signed bitvectors.

  SMT-Lib name: `bvsmulo`.
-/

def smulOverflow {w : Nat} (x y : BitVec w) : Bool :=
  (x.toInt * y.toInt ≥ 2 ^ (w - 1)) || (x.toInt * y.toInt < - 2 ^ (w - 1))

/--
  Count the number of leading zeroes downward from the 'n'th bit to the '0'th bit.
-/
def clzAux {w : Nat} (x : BitVec w) (n : Nat) : Nat :=
  match n with
  | 0 => if x.getLsbD 0 then 0 else 1
  | n' + 1 =>
    if x.getLsbD n then 0
      else 1 + clzAux x n'

/-- Count the number of leading zeroes. -/
def clz {w : Nat} (x : BitVec w) : BitVec w := if w = 0 then 0 else BitVec.ofNat w (clzAux x (w - 1))

end BitVec
