import Std.Tactic.Do

/-!
# Lean transcription and verification of the built-in MPN bignum implementation

`src/runtime/mpn.cpp` implements multi-precision naturals as little-endian arrays of `uint32_t`
digits. It is the arithmetic Lean uses when built with `USE_GMP=OFF`, and under that flag it is
part of the TCB.

`type_checker::reduce_nat` reduces `Nat.succ`, `add`, `sub`, `mul`, `pow`, `gcd`, `mod`, `div`,
`beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft` and `shiftRight`. This file follows all fifteen
down through the three layers they pass through.

`lean_object` is the outermost: a `Nat` is a tagged scalar or a pointer to an `mpz`. `NatObj`
carries that choice with the invariant `mpz_to_nat` maintains, and `natAdd_val` and its siblings
prove each operation computes what `Nat` does. The three that can panic assume the condition under
which they do not, rather than discharging it; nothing above this layer is modelled, so those
are the only assumptions the file rests on.

`mpz` is the signed wrapper, whose non-negative part is `Num`. `Num.val_add` and its siblings prove
that layer. The `Num` type carries the normalization `mpz::set` establishes, so the preconditions
`mpn` needs are discharged structurally rather than assumed.

`mpn` is the bottom. `denote_add`, `denote_sub`, `denote_mul`, `div_spec` and `compare_spec` prove
`mpn_add`, `mpn_sub`, `mpn_mul`, `mpn_div` (by way of Knuth's Algorithm D) and `mpn_compare`.
`mpn_to_string` is not modelled, since `reduce_nat` never reaches it.

C++ leaves an operation undefined outside a range, and this file carries the bound that rules that
out wherever the bound is actually known. A local bound is an argument of the operation, so a use
site cannot be written without discharging it: the shifts and divisions of `CPP` take the hypothesis
that pins each down, and a buffer a routine fills itself is a `Vector` whose length bounds every
write by construction. A bound that is instead a fact about the whole computation cannot be an
argument, since it is not known where the write happens: a buffer a caller owns is written with
`set!` and read with `getD`, both total, and the index staying in range is proved in the
specification rather than the type, as `div_1` and `div_n` do. Where a routine asserts a fact that a
release build then drops, since `lean_assert` is `DEBUG_CODE`, the branch resting on it is proved
here instead, by the specification that covers it: the `small`/`big` arm of `natDiv` and the arms of
`natSub`, `natMod`, `natBle` and `natBeq` that answer without computing.

Each definition quotes the code it stands for, so the two can be read side by side without opening
the source. Deviations are marked `NOTE:`. Each routine is transliterated whole; where a proof
needs the loop's length or buffers free, the loop is repeated as a `private` helper. Its invariant
is proved about the helper and consumed at the routine, which typechecks only while the two agree,
so a divergence between them is a compile error.

A transliteration is only worth as much as its fidelity to the original, and nothing here checks
that mechanically: it rests on reading the two side by side, which is what the quotations are for.
-/
open Std Do
set_option linter.deprecated.syntax false

namespace Mpn

/-!
## The operations C++ leaves undefined

Lean's operations are total where C++'s are not: `x <<< d` masks the shift
amount to `d % 32`, where the standard leaves a shift by at least the width of
the promoted left operand undefined, and division by zero is zero, where the
standard leaves it undefined. That makes a direct transliteration *defined*
where the original is not, which is only sound while the undefined cases are
unreachable.

Each operation below wraps one of them with the hypothesis that pins it down.
Taking the hypothesis in the definition rather than in a theorem about it means
a use site cannot be written without discharging it, so the preconditions
propagate to the callers that establish them instead of being restated at each
specification.

`size_t` underflow is deliberately absent: unsigned arithmetic is defined to
wrap modulo 2^64, and `mpn.cpp` leans on that, using counters that wrap to
`(size_t)-1` as the termination sentinel of a downward loop.

Out-of-range indexing is undefined too, but it is not here: its bound is a fact
about the algorithm rather than about the operation, so a buffer a caller owns
is indexed totally, with `getD` and `set!`, and kept in range by the
specification. Only the buffers a routine fills itself carry their bound, as the
`Vector` length that makes each write intrinsic.
-/
namespace CPP

/-- `x << d` on `unsigned int`. -/
@[simp] def shl (x : UInt32) (d : Nat) (_h : d < 32) : UInt32 := x <<< UInt32.ofNat d

/-- `x >> d` on `unsigned int`. -/
@[simp] def shr (x : UInt32) (d : Nat) (_h : d < 32) : UInt32 := x >>> UInt32.ofNat d

/-- `t << d` on `uint64_t`. -/
@[simp] def shlD (t : UInt64) (d : Nat) (_h : d < 64) : UInt64 := t <<< UInt64.ofNat d

/-- `t >> d` on `uint64_t`. -/
@[simp] def shrD (t : UInt64) (d : Nat) (_h : d < 64) : UInt64 := t >>> UInt64.ofNat d

/-- `a / b` on `uint64_t`; division by zero is undefined. -/
@[simp] def divD (a b : UInt64) (_h : b ≠ 0) : UInt64 := a / b

/-- `a % b` on `uint64_t`. -/
@[simp] def modD (a b : UInt64) (_h : b ≠ 0) : UInt64 := a % b

/-- `a / b` on `unsigned int`. -/
@[simp] def div (a b : UInt32) (_h : b ≠ 0) : UInt32 := a / b

/-- `a % b` on `unsigned int`. -/
@[simp] def mod (a b : UInt32) (_h : b ≠ 0) : UInt32 := a % b

end CPP


section Digits

/-- `mpn_digit`, which `mpn.h` fixes at `uint32_t`. -/
abbrev Digit := UInt32

/-- `typedef uint64_t mpn_double_digit;` -/
abbrev DoubleDigit := UInt64

/-- `sizeof(mpn_digit)`, which `mpn.h` fixes at 4. -/
@[reducible] def digitBytes : Nat := 4

/-- `#define DIGIT_BITS (sizeof(mpn_digit)*8)` -/
@[reducible] def digitBits : Nat := digitBytes * 8

/-- `#define BASE ((mpn_double_digit)0x01 << DIGIT_BITS)` -/
def base : Nat := 1 <<< digitBits

/-- `#define MASK_FIRST (~((mpn_digit)(-1) >> 1))` -/
def maskFirst : Digit := ~~~((-1 : Digit) >>> 1)

/--
`c[i+j] = (t << DIGIT_BITS) >> DIGIT_BITS`, the low word of a double digit. The
`toUInt32` is the narrowing the assignment to an `mpn_digit` performs.
-/
private def lo (t : DoubleDigit) : Digit :=
  (CPP.shrD (CPP.shlD t digitBits (by decide)) digitBits (by decide)).toUInt32

/-- `k = t >> DIGIT_BITS`, the high word, narrowed the same way. -/
private def hi (t : DoubleDigit) : Digit :=
  (CPP.shrD t digitBits (by decide)).toUInt32

/-! ## Denotation -/

/-- The first `j` digits of `a`, little-endian, read as a natural. -/
def denoteN (a : Array Digit) : Nat → Nat
  | 0 => 0
  | j+1 => denoteN a j + (a.getD j 0).toNat * base ^ j

/-- `a` read as a little-endian base-`2^32` natural. -/
def denote (a : Array Digit) : Nat := denoteN a a.size

end Digits

section DigitProofs


/-!
The definitions above spell the macros out as `mpn.h` writes them; the
arithmetic below wants their values, and `omega` needs a literal rather than a
shift.
-/

@[simp] theorem digitBits_eq : digitBits = 32 := rfl

@[simp] theorem base_eq : base = 4294967296 := rfl

@[simp] theorem maskFirst_eq : maskFirst = 0x80000000 := rfl

/-! ## Digit-level bit facts

These are about `UInt32` alone, so they sit ahead of everything that uses them.
-/

theorem toNat_shl (x : Digit) {d : Nat} (hd : d < digitBits) :
    (x <<< (UInt32.ofNat d)).toNat = (x.toNat * 2 ^ d) % base := by
  have hm : (UInt32.ofNat d).toNat % 32 = d := by simp [digitBits_eq] at hd ⊢; omega
  rw [UInt32.toNat_shiftLeft, hm, Nat.shiftLeft_eq]
  rfl

theorem toNat_shr (y : Digit) {e : Nat} (he : e < digitBits) :
    (y >>> (UInt32.ofNat e)).toNat = y.toNat / 2 ^ e := by
  have hm : (UInt32.ofNat e).toNat % 32 = e := by simp [digitBits_eq] at he ⊢; omega
  rw [UInt32.toNat_shiftRight, hm, Nat.shiftRight_eq_div_pow]

private theorem and_top_eq_zero_iff {y : Nat} (hy : y < 4294967296) :
    (y &&& 2147483648 = 0) ↔ y < 2147483648 := by
  have hpow : (2147483648 : Nat) = 2 ^ 31 := rfl
  constructor
  · intro h
    have hb : y.testBit 31 = false := by
      by_cases hb : y.testBit 31
      · exfalso
        have hand : (y &&& 2147483648).testBit 31 = true := by grind
        rw [h] at hand; simp at hand
      · simpa using hb
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    simp only [decide_eq_false_iff_not] at hb
    omega
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, hpow, Nat.testBit_two_pow]
    by_cases h31 : (31 : Nat) = i
    · grind
    · simp [h31]

/-- `div_normalize`'s `(x << d) & MASK_FIRST == 0` test reads the top bit. -/
private theorem topBit_test (y : Digit) :
    (y &&& maskFirst == 0) = decide (y.toNat < 2147483648) := by
  have hy : y.toNat < 4294967296 := y.toNat_lt_size
  have hand : (y &&& maskFirst).toNat = y.toNat &&& 2147483648 := rfl
  have hiff : (y &&& maskFirst = 0) ↔ y.toNat < 2147483648 := by
    constructor
    · intro h
      have h0 : (y &&& maskFirst).toNat = 0 := by rw [h]; rfl
      exact (and_top_eq_zero_iff hy).mp h0
    · intro h
      have h0 : y.toNat &&& 2147483648 = 0 := (and_top_eq_zero_iff hy).mpr h
      rw [← hand] at h0
      exact UInt32.toNat_inj.mp (by rw [h0]; rfl)
  grind

/--
Recombining two adjacent digits under a left shift by `d`: the `|` in
`div_normalize` cannot carry, because the low `d` bits of the shifted digit are
zero and the bits arriving from below are less than `2^d`.
-/
theorem toNat_shl_or_shr (x y : Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits) :
    ((x <<< (UInt32.ofNat d)) ||| (y >>> (UInt32.ofNat (digitBits - d)))).toNat
      = (x.toNat * 2 ^ d) % base + y.toNat / 2 ^ (digitBits - d) := by
  simp only [digitBits_eq] at hd hd0 ⊢
  have hy : y.toNat < 2 ^ 32 := y.toNat_lt_size
  have hlt : y.toNat / 2 ^ (32 - d) < 2 ^ d := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show 32 - d + d = 32 by omega]
    exact hy
  have hsplit : (x.toNat * 2 ^ d) % base = (x.toNat % 2 ^ (32 - d)) <<< d := by
    have hb : base = 2 ^ (32 - d) * 2 ^ d := by
      rw [← Nat.pow_add, show 32 - d + d = 32 by omega]; rfl
    rw [hb, Nat.mul_mod_mul_right, Nat.shiftLeft_eq]
  rw [UInt32.toNat_or, toNat_shl x (by simp [digitBits_eq]; omega),
    toNat_shr y (by simp [digitBits_eq]; omega), hsplit, Nat.shiftLeft_add_eq_or_of_lt hlt]

/-!
## Facts about the denotation

These are about `denoteN` and the arrays it reads, so they sit ahead of every
routine that denotes one.
-/

theorem size_set! (a : Array Digit) (i : Nat) (d : Digit) : (a.set! i d).size = a.size :=
  Array.size_setIfInBounds

theorem getD_lt (a : Array Digit) (j : Nat) : (a.getD j 0).toNat < base := by
  simp only [Array.getD]
  split <;> exact UInt32.toNat_lt_size ..

theorem getD_of_ge (a : Array Digit) {j : Nat} (h : a.size ≤ j) : a.getD j 0 = 0 := by grind

theorem getD_push_lt (c : Array Digit) (d : Digit) {j : Nat} (h : j < c.size) :
    (c.push d).getD j 0 = c.getD j 0 := by
  simp [Array.getElem?_push, Nat.ne_of_lt h]

theorem getD_push_eq (c : Array Digit) (d : Digit) : (c.push d).getD c.size 0 = d := by simp

theorem getD_pop_lt (c : Array Digit) {j : Nat} (h : j < c.pop.size) :
    c.pop.getD j 0 = c.getD j 0 := by
  simp only [Array.size_pop] at h
  have hj : j < c.size := by omega
  simp [h, hj]

theorem denoteN_lt (a : Array Digit) (j : Nat) : denoteN a j < base ^ j := by
  induction j with
  | zero => simp [denoteN]
  | succ j ih =>
    have hd := getD_lt a j
    have key : base ^ j + (base - 1) * base ^ j = base ^ (j+1) := by
      rw [base_eq]; omega
    calc denoteN a j + (a.getD j 0).toNat * base ^ j
        < base ^ j + (base - 1) * base ^ j :=
          Nat.add_lt_add_of_lt_of_le ih (Nat.mul_le_mul_right _ (by omega))
      _ = base ^ (j+1) := key

/-- Digits past the end of `a` are zero, so `denoteN` saturates at `a.size`. -/
theorem denoteN_of_ge (a : Array Digit) {j : Nat} (h : a.size ≤ j) :
    denoteN a j = denote a := by
  induction j with
  | zero => have : a.size = 0 := by omega
            simp [denote, this]
  | succ j ih =>
    rcases Nat.lt_or_ge j a.size with h' | h'
    · have : a.size = j + 1 := by omega
      simp [denote, this]
    · simp [denoteN, getD_of_ge a h', ih h']

theorem denoteN_push (c : Array Digit) (d : Digit) {j : Nat} (h : j ≤ c.size) :
    denoteN (c.push d) j = denoteN c j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [denoteN, denoteN, ih (by omega), getD_push_lt c d (by omega)]

theorem denote_push (c : Array Digit) (d : Digit) :
    denote (c.push d) = denote c + d.toNat * base ^ c.size := by
  have hsz : (c.push d).size = c.size + 1 := by simp
  simp only [denote, hsz, denoteN, getD_push_eq, denoteN_push c d (Nat.le_refl _)]

theorem denoteN_pop (c : Array Digit) {j : Nat} (h : j ≤ c.pop.size) :
    denoteN c.pop j = denoteN c j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [denoteN, denoteN, ih (by omega), getD_pop_lt c (by omega)]

/-- Dropping a trailing zero digit does not change the denotation. -/
theorem denote_pop_of_back_zero (c : Array Digit) (h : 0 < c.size)
    (hz : c.getD (c.size - 1) 0 = 0) : denote c.pop = denote c := by
  have hsz : c.pop.size = c.size - 1 := Array.size_pop
  have hlast : c.getD c.pop.size 0 = 0 := by grind
  have hexpand : denote c = denoteN c (c.pop.size + 1) := by
    rw [denote]; congr 1; omega
  rw [hexpand, denoteN, hlast]
  simpa [denote] using denoteN_pop c (Nat.le_refl c.pop.size)

theorem getD_set!_ne (c : Array Digit) (idx n : Nat) (d : Digit) (h : n ≠ idx) :
    (c.set! idx d).getD n 0 = c.getD n 0 := by
  simp [Ne.symm h]

theorem getD_set!_eq (c : Array Digit) (idx : Nat) (d : Digit) (h : idx < c.size) :
    (c.set! idx d).getD idx 0 = d := by
  simp [h]

theorem getD_replicate_zero (n i : Nat) : (Array.replicate n (0 : Digit)).getD i 0 = 0 := by
  simp [Array.getElem?_replicate]; split <;> rfl

private theorem array_ext_getD {a b : Array Digit} (hs : a.size = b.size)
    (h : ∀ i, a.getD i 0 = b.getD i 0) : a = b :=
  Array.ext hs fun i h1 h2 => by
    have hi := h i
    simpa [Array.getD, h1, h2] using hi

/-- `denoteN` only looks at the first `n` digits. -/
theorem denoteN_congr {c c' : Array Digit} {n : Nat}
    (h : ∀ i, i < n → c.getD i 0 = c'.getD i 0) : denoteN c n = denoteN c' n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [denoteN, denoteN, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem denoteN_replicate_zero (n m : Nat) :
    denoteN (Array.replicate n (0 : Digit)) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [denoteN, ih, getD_replicate_zero]; simp

theorem denote_replicate_zero (n : Nat) : denote (Array.replicate n (0 : Digit)) = 0 :=
  denoteN_replicate_zero n _

theorem denoteN_set!_of_le (c : Array Digit) (idx : Nat) (d : Digit) {n : Nat} (h : n ≤ idx) :
    denoteN (c.set! idx d) n = denoteN c n :=
  denoteN_congr fun i hi => getD_set!_ne c idx i d (by omega)

theorem denoteN_set!_succ (c : Array Digit) (idx : Nat) (d : Digit) (h : idx < c.size) :
    denoteN (c.set! idx d) (idx + 1) = denoteN c idx + d.toNat * base ^ idx := by
  rw [denoteN, denoteN_set!_of_le c idx d (Nat.le_refl _), getD_set!_eq c idx d h]

/-- Zero digits from `n` up do not contribute, so `denoteN` saturates at `n`. -/
theorem denoteN_of_high_zero (c : Array Digit) {n m : Nat} (hnm : n ≤ m)
    (h : ∀ idx, n ≤ idx → c.getD idx 0 = 0) : denoteN c m = denoteN c n := by
  induction m with
  | zero => grind
  | succ m ih =>
    rcases Nat.lt_or_ge m n with h' | h'
    · grind
    · simp [denoteN, h m h', ih h']

theorem denote_of_high_zero (c : Array Digit) {n : Nat} (hn : n ≤ c.size)
    (h : ∀ idx, n ≤ idx → c.getD idx 0 = 0) : denote c = denoteN c n :=
  denoteN_of_high_zero c hn h

end DigitProofs

section MpnModel

/-! ## `mpn_compare` -/

/--
`mpn_compare`:
```
int mpn_compare(mpn_digit const * a, size_t const lnga,
                mpn_digit const * b, size_t const lngb) {
    int res = 0;

    size_t j = max(lnga, lngb) - 1;
    for (; j != (size_t)-1 && res == 0; j--) {
        mpn_digit const & u_j = (j < lnga) ? a[j] : zero;
        mpn_digit const & v_j = (j < lngb) ? b[j] : zero;
        if (u_j > v_j)
            res = 1;
        else if (u_j < v_j)
            res = -1;
    }
    return res;
}
```
The `res == 0` in the loop condition is what stops it at the first difference,
which the `break` here stands for.
-/
def compare (a b : Array Digit) : Int := Id.run do
  let mut res : Int := 0
  for j in (List.range (max a.size b.size)).reverse do
    if res != 0 then break
    let u_j := a.getD j 0
    let v_j := b.getD j 0
    if u_j > v_j then res := 1
    else if u_j < v_j then res := -1
  return res

/-! ## `mpn_add` -/

/--
`mpn_add`'s trimming of the result length:
```
    size_t &os = *plngc;
    for (os = len+1; os > 1 && c[os-1] == 0; ) os--;
```
-/
def trim (c : Array Digit) : Array Digit := Id.run do
  let mut c := c
  while 1 < c.size && c.getD (c.size - 1) 0 == 0 do
    c := c.pop
  return c

/--
`mpn_add`, Knuth's Algorithm A:
```
void  mpn_add(mpn_digit const * a, size_t const lnga,
              mpn_digit const * b, size_t const lngb,
              mpn_digit * c, size_t const lngc_alloc,
              size_t * plngc) {
    // Essentially Knuth's Algorithm A
    size_t len = max(lnga, lngb);
    lean_assert(lngc_alloc == len+1 && len > 0);
    mpn_digit k = 0;
    mpn_digit r;
    bool c1, c2;
    for (size_t j = 0; j < len; j++) {
        mpn_digit const & u_j = (j < lnga) ? a[j] : zero;
        mpn_digit const & v_j = (j < lngb) ? b[j] : zero;
        r = u_j + v_j; c1 = r < u_j;
        c[j] = r + k;  c2 = c[j] < r;
        k = c1 | c2;
    }
    c[len] = k;
    size_t &os = *plngc;
    for (os = len+1; os > 1 && c[os-1] == 0; ) os--;
    lean_assert(os > 0 && os <= len+1);
}
```
The caller allocates `c` with `lngc_alloc` digits and reads the trimmed length
back out of `*plngc`. Here the trimmed prefix is the result, so neither appears.

NOTE: `c` is written by index and pushed here. The digits are the same sequence,
and `c.size` becomes the loop counter, so `denote_push` carries a whole iteration
and `addLoop_spec` can induct on `len` without also tracking that the digits
above it are untouched.
-/
def add (a b : Array Digit) : Array Digit := Id.run do
  let len := max a.size b.size
  let mut c : Array Digit := #[]
  let mut k : Digit := 0
  for j in List.range len do
    let u_j := a.getD j 0
    let v_j := b.getD j 0
    let r := u_j + v_j; let c1 := r < u_j
    let cj := r + k; let c2 := cj < r
    c := c.push cj
    k := if c1 || c2 then 1 else 0
  c := c.push k
  return trim c

/-! ## `mpn_sub` -/

/--
`mpn_sub`, Knuth's Algorithm S:
```
void mpn_sub(mpn_digit const * a, size_t const lnga,
             mpn_digit const * b, size_t const lngb,
             mpn_digit * c, mpn_digit * pborrow) {
    // Essentially Knuth's Algorithm S
    size_t len = max(lnga, lngb);
    mpn_digit & k = *pborrow; k = 0;
    mpn_digit r;
    bool c1, c2;
    for (size_t j = 0; j < len; j++) {
        mpn_digit const & u_j = (j < lnga) ? a[j] : zero;
        mpn_digit const & v_j = (j < lngb) ? b[j] : zero;
        r = u_j - v_j; c1 = r > u_j;
        c[j] = r - k;  c2 = c[j] > r;
        k = c1 | c2;
    }
}
```
NOTE: `c` is written by index into a buffer the caller allocates with `len`
digits and pushed here, for the reason given at `add`. The borrow leaves
through `*pborrow`, which is the second result.
-/
def sub (a b : Array Digit) : Array Digit × Digit := Id.run do
  let len := max a.size b.size
  let mut c : Array Digit := #[]
  let mut k : Digit := 0
  for j in List.range len do
    let u_j := a.getD j 0
    let v_j := b.getD j 0
    let r := u_j - v_j; let c1 := r > u_j
    let cj := r - k; let c2 := cj > r
    c := c.push cj
    k := if c1 || c2 then 1 else 0
  return (c, k)

/--
`mpn_sub`'s digit loop, writing its result back over its first operand, which is
how `div_n` calls it:
```
        mpn_sub(&numer[j], n+1, ms.data(), n+1, &numer[j], &borrow);
```
Each iteration reads `u[off+i]` and then writes it, and no later iteration reads
it again, so the aliasing is safe. `subInPlace_spec` below is that statement:
the result agrees digit for digit with running `mpn_sub` into a separate buffer.
-/
-- NOTE: `set!` writes `u[off+i]` for `i < len`; these land in range under
-- `off + len ≤ u.size`, which `subInPlace_spec` takes as `hfits` and the caller
-- (`div_n`, through `divNLoop_spec`) establishes. The out-of-range no-op is
-- unreachable, so it stands for nothing the C++ does.
def subInPlace (u b : Array Digit) (off len : Nat) : Array Digit × Digit := Id.run do
  let mut u := u
  let mut k : Digit := 0
  for i in List.range len do
    let u_i := u.getD (off + i) 0
    let v_i := b.getD i 0
    let r := u_i - v_i
    let c1 := r > u_i
    let ci := r - k
    let c2 := ci > r
    u := u.set! (off + i) ci
    k := if c1 || c2 then 1 else 0
  return (u, k)

/-! ## `mpn_mul` -/

/--
`mpn_mul`, Knuth's Algorithm M, returning `lnga + lngb` digits:
```
void mpn_mul(mpn_digit const * a, size_t const lnga,
             mpn_digit const * b, size_t const lngb,
             mpn_digit * c) {
    for (unsigned i = 0; i < lnga; i++)
        c[i] = 0;

    for (size_t j = 0; j < lngb; j++) {
        mpn_digit const & v_j = b[j];
        if (v_j == 0) { // This branch may be omitted according to Knuth.
            c[j+lnga] = 0;
        }
        else {
            k = 0;
            for (i = 0; i < lnga; i++) { ... }
            c[j+lnga] = k;
        }
    }
}
```
NOTE: `mpn_mul` zeroes only `c[0..lnga)` and relies on the outer loop to write
every digit from `lnga` up; zeroing the whole buffer here computes the same
result and states the invariant more simply.
-/
def mul (a b : Array Digit) : Array Digit := Vector.toArray <| Id.run do
  let mut c : Vector Digit (a.size + b.size) := Vector.replicate (a.size + b.size) 0
  for j in List.finRange b.size do
    let v_j := b.getD j.val 0
    if v_j == 0 then
      c := c.set (j.val + a.size) 0 (by omega)
    else
      let mut k : Digit := 0
      for i in List.finRange a.size do
        let u_i := a.getD i.val 0
        let t : DoubleDigit :=
          u_i.toUInt64 * v_j.toUInt64 + (c.getD (i.val + j.val) 0).toUInt64 + k.toUInt64
        c := c.set (i.val + j.val) (lo t) (by omega)
        k := hi t
      c := c.set (j.val + a.size) k (by omega)
  return c

/-! ## division -/

private theorem toUInt64_ne_zero {x : Digit} (h : 0 < x.toNat) : x.toUInt64 ≠ 0 := by
  intro h0
  have hz : x.toUInt64.toNat = 0 := by rw [h0]; rfl
  rw [UInt32.toNat_toUInt64] at hz
  omega

theorem sub_digitBits_lt {d : Nat} (h : 0 < d) : digitBits - d < digitBits := by
  simp only [digitBits_eq]; omega

/--
The leading-zero count of `x`, as `div_normalize`'s `while` loop computes it:
```
    size_t d = 0;
    while (lden > 0 && ((denom[lden-1] << d) & MASK_FIRST) == 0) d++;
```
NOTE: that loop shifts by `d == 32` once the top denominator digit is zero,
which is undefined, and under a masking shift never terminates. This one stops
at `digitBits - 1` instead, and carries the bound in its type, so that every
shift it feeds is well defined without a side condition. Callers reach
`mpn_div` only through `mpz`, whose sizes are normalized, so the top digit is
nonzero unless the denominator is zero, which `lean_nat_div` rejects first.
-/
def leadingZeros (x : Digit) : Fin digitBits :=
  go 0 (by simp [digitBits_eq])
where
  /-- `d++` in the `while` loop, from `d` up. -/
  go (d : Nat) (hd : d < digitBits) : Fin digitBits :=
    if h : d + 1 < digitBits then
      if CPP.shl x d hd &&& maskFirst == 0 then go (d + 1) h else ⟨d, hd⟩
    else ⟨d, hd⟩
  termination_by digitBits - d
  decreasing_by simp only [digitBits_eq] at *; omega

/-- The predicate `leadingZeros` counts, in arithmetic terms. -/
private theorem leadingZeros_pred (x : Digit) {i : Nat} (hi : i < digitBits) :
    (CPP.shl x i hi &&& maskFirst == 0)
      = decide (x.toNat * 2 ^ i % base < 2147483648) := by
  rw [CPP.shl, topBit_test, toNat_shl x hi]

/--
`div_normalize` shifts by exactly enough to set the top bit of the leading
denominator digit: the shifted digit lands in `[2^31, 2^32)`, which is what
normalization means and what Knuth's Algorithm D assumes of its divisor.
-/
theorem leadingZerosGo_spec (x : Digit) (hx : 0 < x.toNat) (d : Nat) (hd : d < digitBits)
    (hfit : x.toNat * 2 ^ d < base) :
    2147483648 ≤ x.toNat * 2 ^ (leadingZeros.go x d hd).val ∧
      x.toNat * 2 ^ (leadingZeros.go x d hd).val < base := by
  have hmod : x.toNat * 2 ^ d % base = x.toNat * 2 ^ d := Nat.mod_eq_of_lt hfit
  rw [leadingZeros.go]
  split <;> rename_i h
  · split <;> rename_i hp
    · -- the top bit is still clear, so the value can double and stay in range
      have hpe := leadingZeros_pred x hd
      have hlt : x.toNat * 2 ^ d < 2147483648 := by grind
      exact leadingZerosGo_spec x hx (d+1) h (by
        rw [Nat.pow_succ, ← Nat.mul_assoc]; simp only [base_eq] at hlt ⊢; omega)
    · -- the top bit is set, so this is the shift `div_normalize` reports
      have hpe := leadingZeros_pred x hd
      have hge : ¬ (x.toNat * 2 ^ d < 2147483648) := by grind
      refine ⟨?_, hfit⟩
      show 2147483648 ≤ x.toNat * 2 ^ d
      omega
  · -- the last shift the loop can take; a nonzero digit already reaches the top
    have hb : digitBits = 32 := rfl
    grind
termination_by digitBits - d
decreasing_by simp only [digitBits_eq] at *; omega

theorem leadingZeros_spec (x : Digit) (hx : 0 < x.toNat) :
    2147483648 ≤ x.toNat * 2 ^ (leadingZeros x).val ∧
      x.toNat * 2 ^ (leadingZeros x).val < base :=
  leadingZerosGo_spec x hx 0 (by simp [digitBits_eq])
    (by simp only [Nat.pow_zero, Nat.mul_one]; exact x.toNat_lt_size)


/-!
`div_normalize` resizes its buffers and then writes them by index. The buffers
below are `Vector`s, so their length is in the type and each write carries the
bound it needs. These reduce such a loop to the map its proofs read digitwise.
-/

/--
Each write puts `g i` at index `i`, so once `i` is in the list the fold holds `g i`
there whatever came before.
-/
private theorem getElem_foldl_vset (g : Nat → Digit) (n : Nat) :
    ∀ (l : List (Fin n)) (v : Vector Digit n) (i : Nat) (hi : i < n),
      (l.foldl (fun (b : Vector Digit n) (j : Fin n) => b.set j.val (g j.val) j.isLt) v)[i]
        = if (⟨i, hi⟩ : Fin n) ∈ l then g i else v[i] := by
  intro l
  induction l with
  | nil => intro v i hi; simp
  | cons j l ih =>
    intro v i hi
    rw [List.foldl_cons, ih]
    simp only [List.mem_cons, Vector.getElem_set, Fin.ext_iff]
    split <;> split <;> simp_all <;> omega

/-- Filling a zeroed buffer index by index is the map the shift proofs read. -/
private theorem toArray_foldl_vset (g : Nat → Digit) (n : Nat) :
    ((List.finRange n).foldl
        (fun (b : Vector Digit n) (i : Fin n) => b.set i.val (g i.val) i.isLt)
        (Vector.replicate n 0)).toArray
      = (Array.range n).map g := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Vector.getElem_toArray, getElem_foldl_vset, List.mem_finRange, ite_true,
      Array.getElem_map, Array.getElem_range]

/-- The shift loops' shared shape: filling a zeroed buffer index by index is the map. -/
private theorem shiftLoop_eq (g : Nat → Digit) (n : Nat) :
    (Id.run do
      let mut out : Vector Digit n := Vector.replicate n 0
      for i in List.finRange n do
        out := out.set i.val (g i.val) i.isLt
      return out.toArray) = (Array.range n).map g := by
  simp [Id.run]
  exact toArray_foldl_vset g n

/--
`len` digits of `a` shifted left by `d` bits, which is what both of
`div_normalize`'s shifting loops do:
```
        mpn_digit q = FIRST_BITS(d, numer[lnum-1]);
        n_numer[lnum] = q;
        for (size_t i = lnum-1; i > 0; i--)
            n_numer[i] = (numer[i] << d) | FIRST_BITS(d, numer[i-1]);
        n_numer[0] = numer[0] << d;
```
Each output digit reads only the input, so the loop is written here as the map
it is. The `d == 0` case is separate because C++ needs it to be: shifting a digit by
32 is undefined.
-/
def shiftLeftDigits (a : Array Digit) (d len : Nat) (hd : d < digitBits) : Array Digit :=
    Id.run do
  let mut out : Vector Digit len := Vector.replicate len 0
  for i in List.finRange len do
    out := out.set i.val (
      if h : d = 0 then a.getD i.val 0
      else CPP.shl (a.getD i.val 0) d hd |||
        (if i.val == 0 then 0
         else CPP.shr (a.getD (i.val-1) 0) (digitBits - d) (sub_digitBits_lt (by omega)))) i.isLt
  return out.toArray

/-- The loop as the map its proofs read digitwise. -/
theorem shiftLeftDigits_eq (a : Array Digit) (d len : Nat) (hd : d < digitBits) :
    shiftLeftDigits a d len hd = (Array.range len).map (fun i =>
      if h : d = 0 then a.getD i 0
      else CPP.shl (a.getD i 0) d hd |||
        (if i == 0 then 0
         else CPP.shr (a.getD (i-1) 0) (digitBits - d) (sub_digitBits_lt (by omega)))) := by
  unfold shiftLeftDigits
  exact shiftLoop_eq (fun i =>
    if h : d = 0 then a.getD i 0
    else CPP.shl (a.getD i 0) d hd |||
      (if i == 0 then 0
       else CPP.shr (a.getD (i-1) 0) (digitBits - d) (sub_digitBits_lt (by omega)))) len

theorem size_shiftLeftDigits (a : Array Digit) (d len : Nat) (hd : d < digitBits) :
    (shiftLeftDigits a d len hd).size = len := by simp [shiftLeftDigits_eq]


private theorem getD_shiftLeftDigits_zero (a : Array Digit) (len j : Nat) (hj : j < len)
    (hd : 0 < digitBits) : (shiftLeftDigits a 0 len hd).getD j 0 = a.getD j 0 := by
  simp [shiftLeftDigits_eq, hj]

private theorem getD_shiftLeftDigits_head (a : Array Digit) {d len : Nat} (hd0 : 0 < d)
    (hd : d < digitBits) (hlen : 0 < len) :
    (shiftLeftDigits a d len hd).getD 0 0 = a.getD 0 0 <<< UInt32.ofNat d := by
  simp [shiftLeftDigits_eq, hlen, Nat.ne_of_gt hd0]

private theorem getD_shiftLeftDigits_tail (a : Array Digit) {d len j : Nat} (hd0 : 0 < d)
    (hd : d < digitBits) (hj : j < len) (hj0 : j ≠ 0) :
    (shiftLeftDigits a d len hd).getD j 0
      = (a.getD j 0 <<< UInt32.ofNat d) ||| (a.getD (j-1) 0 >>> UInt32.ofNat (digitBits - d)) := by
  simp [shiftLeftDigits_eq, hj, Nat.ne_of_gt hd0, hj0]

/-- Shifting a digit left can only add to it, never lose its own bits. -/
private theorem le_getD_shiftLeftDigits (a : Array Digit) {d len j : Nat} (hd : d < digitBits)
    (hj : j < len) :
    (a.getD j 0).toNat * 2 ^ d % base ≤ ((shiftLeftDigits a d len hd).getD j 0).toNat := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    rw [getD_shiftLeftDigits_zero a len j hj hd, Nat.mul_one]
    exact Nat.mod_le _ _
  · rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [getD_shiftLeftDigits_head a hd0 hd (by omega), toNat_shl _ hd]
      exact Nat.le_refl _
    · rw [getD_shiftLeftDigits_tail a hd0 hd hj (by omega), toNat_shl_or_shr _ _ hd0 hd]
      exact Nat.le_add_right _ _

/--
`div_normalize`. Returns the shift `d` together with the normalized numerator
(`lnum+1` digits) and denominator (`lden` digits):
```
    n_numer.resize(lnum+1);
    n_denom.resize(lden);

    if (d == 0) {
        n_numer[lnum] = 0;
        for (size_t i = 0; i < lnum; i++)
            n_numer[i] = numer[i];
        for (size_t i = 0; i < lden; i++)
            n_denom[i] = denom[i];
    }
    else if (lnum != 0) { ... }
    else {
        d = 0;
    }
    return d;
```
`div_normalize` branches three ways, but its `d == 0` copy is exactly
`shiftLeftDigits` at `d = 0`, so only the degenerate case needs its own branch.

NOTE: with a nonzero shift and an empty numerator `div_normalize` leaves both
buffers zeroed and reports `d = 0`. No caller reaches it: `mpn_div` and `mpn_to_string`
both pass `lnum ≥ 1`.
-/
def divNormalize (numer denom : Array Digit) :
    Fin digitBits × Array Digit × Array Digit :=
  let lnum := numer.size
  let lden := denom.size
  let d : Fin digitBits :=
    if lden = 0 then ⟨0, by simp [digitBits_eq]⟩ else leadingZeros (denom.getD (lden - 1) 0)
  if lnum = 0 && d.val ≠ 0 then
    (⟨0, by simp [digitBits_eq]⟩, Array.replicate (lnum + 1) 0, Array.replicate lden 0)
  else
    (d, shiftLeftDigits numer d.val (lnum + 1) d.isLt, shiftLeftDigits denom d.val lden d.isLt)

/-- Under the preconditions every caller satisfies, `div_normalize` shifts both operands. -/
private theorem divNormalize_eq (numer denom : Array Digit) (hnum : 0 < numer.size)
    (hden : 0 < denom.size) :
    divNormalize numer denom =
      (leadingZeros (denom.getD (denom.size - 1) 0),
       shiftLeftDigits numer (leadingZeros (denom.getD (denom.size - 1) 0)).val (numer.size + 1)
         (leadingZeros (denom.getD (denom.size - 1) 0)).isLt,
       shiftLeftDigits denom (leadingZeros (denom.getD (denom.size - 1) 0)).val denom.size
         (leadingZeros (denom.getD (denom.size - 1) 0)).isLt) := by
  simp [divNormalize, Nat.ne_of_gt hden, Nat.ne_of_gt hnum]


/-- Normalization does not change the denominator's length. -/
theorem divNormalize_size_denom (numer denom : Array Digit) (hnum : 0 < numer.size)
    (hden : 0 < denom.size) : (divNormalize numer denom).2.2.size = denom.size := by
  rw [divNormalize_eq numer denom hnum hden]
  exact size_shiftLeftDigits ..

/--
Normalization leaves the leading denominator digit with its top bit set, so it
is nonzero. That is what `div_1` and `div_n` go on to divide by, and what the
C++ asserts with `lean_assert(denom[lden-1] != 0)` before reaching them.
-/
theorem divNormalize_top_pos (numer denom : Array Digit) (hnum : 0 < numer.size)
    (hden : 0 < denom.size) (htop : 0 < (denom.getD (denom.size - 1) 0).toNat) :
    0 < ((divNormalize numer denom).2.2.getD (denom.size - 1) 0).toNat := by
  obtain ⟨_, hhi⟩ := leadingZeros_spec (denom.getD (denom.size - 1) 0) htop
  have hdlt := (leadingZeros (denom.getD (denom.size - 1) 0)).isLt
  rw [divNormalize_eq numer denom hnum hden]
  dsimp only
  have hle := le_getD_shiftLeftDigits denom
    (len := denom.size) (j := denom.size - 1) hdlt (by omega)
  rw [Nat.mod_eq_of_lt hhi] at hle
  omega

/--
`#define LAST_BITS(N, X) (((X) << (DIGIT_BITS-(N))) >> (DIGIT_BITS-(N)))`

Undefined for `N == 0`, where both shifts are by the operand width, so the
positivity of `d` is taken here rather than assumed by the callers.
-/
def lastBits (x : Digit) (d : Nat) (hd : 0 < d) : Digit :=
  CPP.shr (CPP.shl x (digitBits - d) (sub_digitBits_lt hd)) (digitBits - d) (sub_digitBits_lt hd)

/--
`len` digits of `a` shifted right by `d` bits, which is `div_unnormalize`'s
nonzero-shift branch:
```
        for (size_t i = 0; i < denom.size()-1; i++)
            rem[i] = numer[i] >> d | (LAST_BITS(d, numer[i+1]) << (DIGIT_BITS-d));
        rem[denom.size()-1] = numer[denom.size()-1] >> d;
```
The top digit takes nothing from above, as `div_unnormalize` does, and `d == 0`
is separate for the same reason as in `shiftLeftDigits`.
-/
def shiftRightDigits (a : Array Digit) (d len : Nat) (hd : d < digitBits) : Array Digit :=
    Id.run do
  let mut out : Vector Digit len := Vector.replicate len 0
  for i in List.finRange len do
    out := out.set i.val (
      if h : d = 0 then a.getD i.val 0
      else CPP.shr (a.getD i.val 0) d hd |||
        (if i.val + 1 == len then 0
         else CPP.shl (lastBits (a.getD (i.val+1) 0) d (by omega)) (digitBits - d)
                (sub_digitBits_lt (by omega)))) i.isLt
  return out.toArray

/--
`div_unnormalize`. Produces `lden` remainder digits; the `d == 0` branch is
`shiftRightDigits` at `d = 0`:
```
    if (d == 0) {
        for (size_t i = 0; i < denom.size(); i++)
            rem[i] = numer[i];
    }
    else { ... }
```
-/
def divUnnormalize (numer : Array Digit) (lden d : Nat) (hd : d < digitBits) : Array Digit :=
  shiftRightDigits numer d lden hd

/--
One iteration of `div_1`'s loop, dividing the two-digit window at `j` by `denom`:
```
        temp = (((mpn_double_digit)numer[j]) << DIGIT_BITS) | ((mpn_double_digit)numer[j-1]);
        q_hat = temp / (mpn_double_digit) denom;
        if (q_hat >= BASE) {
            lean_unreachable(); // is this reachable with normalized v?
        }
        ms = temp - (q_hat * (mpn_double_digit) denom);
        borrow = ms > temp;
        numer[j-1] = (mpn_digit) ms;
        numer[j] = ms >> DIGIT_BITS;
        quot[j-1] = (mpn_digit) q_hat;
        if (borrow) {
            quot[j-1]--;
            numer[j] = numer[j-1] + denom;
        }
```
The three `set!` write `numer[j-1]`, `numer[j]` and `quot[j-1]`. They are in
range for the buffer sizes `div1Loop_spec` maintains, so the out-of-range no-op
`set!` would fall to is never reached; that bound lives in the specification, as
the module docstring describes, not in the type here.
-/
def div1Step (denom : Digit) (hden : denom.toUInt64 ≠ 0)
    (s : Array Digit × Array Digit) (j : Nat) : Array Digit × Array Digit :=
  let (u, quot) := s
  let temp : DoubleDigit := ((u.getD j 0).toUInt64 <<< 32) ||| (u.getD (j-1) 0).toUInt64
  let q_hat := CPP.divD temp denom.toUInt64 hden
  let ms := temp - q_hat * denom.toUInt64
  let borrow := ms > temp
  let u := u.set! (j-1) (lo ms)
  let u := u.set! j (hi ms)
  let quot := quot.set! (j-1) (lo q_hat)
  if borrow then
    -- NOTE: dead. `ms` is `temp % denom`, which cannot exceed `temp`, and
    -- `q_hat * denom` cannot overflow because `q_hat` is `temp / denom`.
    (u.set! j ((u.getD (j-1) 0) + denom), quot.set! (j-1) ((quot.getD (j-1) 0) - 1))
  else (u, quot)

/--
`div_1`. Single-digit division; returns the updated numerator (holding the
remainder in its lowest digit) and `numer.size - 1` quotient digits:
```
static void div_1(mpn_buffer & numer, mpn_digit const denom,
                  mpn_digit * quot) {
    mpn_double_digit q_hat, temp, ms;
    mpn_digit borrow;

    for (size_t j = numer.size()-1; j > 0; j--) { ... }
}
```
`quot` is a caller-supplied buffer of `numer.size() - 1` digits, allocated here
as the second component of the state.
-/
def div1 (numer : Array Digit) (denom : Digit) (hden : denom.toUInt64 ≠ 0) :
    Array Digit × Array Digit := Id.run do
  let mut s := (numer, Array.replicate (numer.size - 1) 0)
  for j in (List.range (numer.size - 1)).reverse do
    s := div1Step denom hden s (j+1)
  return s

/--
The `recheck:` correction loop of `div_n`, i.e. step D3 of Knuth's Algorithm D:
```
        recheck:
        if (q_hat >= BASE ||
            ((q_hat * denom[n-2]) > ((r_hat << DIGIT_BITS) + numer[j+n-2]))) {
                q_hat--;
                r_hat += denom[n-1];
                if (r_hat < BASE) goto recheck;
        }
```
The loop terminates because the trial digit strictly decreases on every pass and
the test cannot fire at zero: `q_hat >= BASE` is false there, and
`q_hat * denom[n-2] > ...` reads `0 > ...`. Knuth bounds the loop at two passes,
but that bound is a performance property, not what makes the loop total.
-/
def recheck (dn1 dn2 nu : Digit) (q_hat r_hat : DoubleDigit) : DoubleDigit × DoubleDigit :=
  if q_hat >>> 32 != 0 || q_hat * dn2.toUInt64 > ((r_hat <<< 32) + nu.toUInt64) then
    let q' := q_hat - 1
    let r' := r_hat + dn1.toUInt64
    if r' >>> 32 == 0 then recheck dn1 dn2 nu q' r' else (q', r')
  else (q_hat, r_hat)
termination_by q_hat.toNat
decreasing_by
  rename_i h _
  have hq : q_hat ≠ 0 := by intro h0; subst h0; simp at h
  have h1 : q_hat.toNat ≠ 0 := fun h0 => hq (UInt64.toNat_inj.mp (by rw [h0]; rfl))
  have h2 : q_hat.toNat < 2 ^ 64 := q_hat.toNat_lt_size
  show (q_hat - 1).toNat < q_hat.toNat
  rw [UInt64.toNat_sub, show (1 : UInt64).toNat = 1 from rfl]
  omega

/--
`div_n`'s copy of an add-back result into the numerator window:
```
            for (size_t i = 0; i < n+1; i++)
                numer[j+i] = ab[i];
```
The `set!` writes `dst[j+i]` for `i < len`, in range whenever `j + len ≤
dst.size`; `size_copyInto` and `getD_copyInto_*` characterize the result on that
assumption, which `div_n` meets. The out-of-range no-op is never reached.
-/
def copyInto (dst src : Array Digit) (j : Nat) (len : Nat) : Array Digit := Id.run do
  let mut dst := dst
  for i in List.range len do
    dst := dst.set! (j + i) (src.getD i 0)
  return dst

/--
The trial quotient digit `div_n` forms for the window at `j`, after step D3:
```
        temp = (((mpn_double_digit)numer[j+n]) << DIGIT_BITS) | ((mpn_double_digit)numer[j+n-1]);
        q_hat = temp / (mpn_double_digit) denom[n-1];
        r_hat = temp % (mpn_double_digit) denom[n-1];
```
NOTE: `n-2` is truncated subtraction here, so a denominator shorter than two
digits reads `denom[0]` twice, where `div_n` underflows `n-2` in `size_t` and
reads out of bounds. Neither is reached: `mpn_div` sends `lden == 1` to `div_1`,
`div_n` asserts `denom.size() > 1`, and `divN_spec` assumes `denom.size = k+2`.
-/
def divNTrial (denom u : Array Digit) (hv : (denom.getD (denom.size - 1) 0).toUInt64 ≠ 0)
    (j : Nat) : Digit :=
  let n := denom.size
  let temp : DoubleDigit :=
    ((u.getD (j+n) 0).toUInt64 <<< 32) ||| (u.getD (j+n-1) 0).toUInt64
  let dn1 := (denom.getD (n-1) 0).toUInt64
  let q_hat := CPP.divD temp dn1 hv
  let r_hat := CPP.modD temp dn1 hv
  lo (recheck (denom.getD (n-1) 0) (denom.getD (n-2) 0) (u.getD (j+n-2) 0) q_hat r_hat).1

/--
One iteration of `div_n`'s outer loop, producing quotient digit `j`:
```
        mpn_digit q_hat_small = (mpn_digit)q_hat;
        mpn_mul(&q_hat_small, 1, denom.data(), n, ms.data());
        mpn_sub(&numer[j], n+1, ms.data(), n+1, &numer[j], &borrow);
        quot[j] = q_hat_small;
        if (borrow) {
            quot[j]--;
            ab.resize(n+2);
            size_t real_size;
            mpn_add(denom.data(), n, &numer[j], n+1, ab.data(), n+2, &real_size);
            for (size_t i = 0; i < n+1; i++)
                numer[j+i] = ab[i];
        }
```
The `mpn_sub` writes its result back over `&numer[j]`, its own first operand,
so `subInPlace` is used here rather than `sub`; `subInPlace_eq` is what makes
that aliasing sound.

The `quot.set! j` and the writes inside `subInPlace` and `copyInto` all index
`u` and `quot` within the sizes `divNLoop_spec` maintains, so their bound is
established there rather than here, and no `set!` falls to its out-of-range
no-op.
-/
def divNStep (denom : Array Digit) (hv : (denom.getD (denom.size - 1) 0).toUInt64 ≠ 0)
    (s : Array Digit × Array Digit) (j : Nat) : Array Digit × Array Digit :=
  let (u, quot) := s
  let n := denom.size
  let q_hat_small := divNTrial denom u hv j
  let ms := mul #[q_hat_small] denom
  let (u, borrow) := subInPlace u ms j (n+1)
  if borrow != 0 then
    -- step D6: the estimate was one too high, so add the divisor back
    let ab := add denom (u.extract j (j+n+1))
    (copyInto u ab j (n+1), quot.set! j (q_hat_small - 1))
  else (u, quot.set! j q_hat_small)

/--
`div_n`, i.e. Knuth's Algorithm D. Returns the updated numerator (holding the
normalized remainder) and `m` quotient digits:
```
static void div_n(mpn_buffer & numer, mpn_buffer const & denom,
                  mpn_digit * quot, mpn_digit * rem,
                  mpn_buffer & ms, mpn_buffer & ab) {
    lean_assert(denom.size() > 1);
    size_t m = numer.size() - denom.size();
    size_t n = denom.size();
    lean_assert(numer.size() == m+n);
    ms.resize(n+1);
    for (size_t j = m-1; j != (size_t)-1; j--) { ... }
}
```
`quot` is a caller-supplied buffer of `m` digits, allocated here as the second
component of the state. `ms` and `ab` are scratch buffers that `divNStep`
produces as values instead.
-/
def divN (numer denom : Array Digit) (hv : (denom.getD (denom.size - 1) 0).toUInt64 ≠ 0) :
    Array Digit × Array Digit := Id.run do
  let mut s := (numer, Array.replicate (numer.size - denom.size) 0)
  for j in (List.range (numer.size - denom.size)).reverse do
    s := divNStep denom hv s j
  return s

/--
`mpn_div`. Returns `lnum - lden + 1` quotient digits and `lden` remainder digits:
```
    if (lnum == 1 && lden == 1) {
        *quot = numer[0] / denom[0];
        *rem  = numer[0] % denom[0];
    }
    else if (lnum < lden || (lnum == lden && numer[lnum-1] < denom[lden-1])) {
        *quot = 0;
        for (size_t i = 0; i < lden; i++)
            rem[i] = (i < lnum) ? numer[i] : 0;
    }
    else  {
        mpn_buffer u, v, t_ms, t_ab;
        size_t d = div_normalize(numer, lnum, denom, lden, u, v);
        if (lden == 1)
            div_1(u, v[0], quot);
        else
            div_n(u, v, quot, rem, t_ms, t_ab);
        div_unnormalize(u, v, d, rem);
    }
```
The preconditions are the ones `mpn_div` asserts, and they make its `lnum < lden`
branch dead, which is why it is `absurd` here.

That branch used to zero `quot[0 .. lnum-lden+1)`, a bound computed in `size_t`
that wraps whenever `lden > lnum + 1` and then overruns the buffer. The loop
never legitimately iterates, since `lnum < lden` puts the bound at or below
zero, and it has been removed.
-/
@[simp] def div (numer denom : Array Digit) (hden : 0 < denom.size)
    (hsz : denom.size ≤ numer.size)
    (htop : 0 < (denom.getD (denom.size - 1) 0).toNat) : Array Digit × Array Digit :=
  let lnum := numer.size
  let lden := denom.size
  if hlt : lnum < lden then
    absurd hlt (by omega)
  else if h11 : (lnum = 1 && lden = 1) = true then
    have h1 : denom.getD 0 0 ≠ 0 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h11
      have hz : denom.size - 1 = 0 := by omega
      rw [hz] at htop
      intro h0
      rw [h0] at htop
      simp at htop
    (#[CPP.div (numer.getD 0 0) (denom.getD 0 0) h1],
     #[CPP.mod (numer.getD 0 0) (denom.getD 0 0) h1])
  else if lnum = lden && numer.getD (lnum-1) 0 < denom.getD (lden-1) 0 then
    (Array.replicate (lnum - lden + 1) 0, (Array.range lden).map fun i => numer.getD i 0)
  else
    have hnum : 0 < numer.size := by omega
    have hvsz : (divNormalize numer denom).2.2.size = denom.size :=
      divNormalize_size_denom numer denom hnum hden
    -- one obligation serves both arms: with `lden = 1` the top digit is digit 0
    have hnz : ((divNormalize numer denom).2.2.getD
        ((divNormalize numer denom).2.2.size - 1) 0).toUInt64 ≠ 0 := by
      rw [hvsz]
      exact toUInt64_ne_zero (divNormalize_top_pos numer denom hnum hden htop)
    let d := (divNormalize numer denom).1
    let u := (divNormalize numer denom).2.1
    let v := (divNormalize numer denom).2.2
    let (u, q) := if lden = 1 then div1 u (v.getD (v.size - 1) 0) hnz else divN u v hnz
    let quot := copyInto (Array.replicate (lnum - lden + 1) 0) q 0 (min q.size (lnum - lden + 1))
    (quot, divUnnormalize u lden d.val d.isLt)

end MpnModel

section MpnProofs

/-- The loop above with its length free, so that `subLoop_spec` can induct on it. -/
private def subLoop (a b : Array Digit) (len : Nat) : Array Digit × Digit := Id.run do
  let mut c : Array Digit := #[]
  let mut k : Digit := 0
  for j in List.range len do
    let u_j := a.getD j 0
    let v_j := b.getD j 0
    let r := u_j - v_j; let c1 := r > u_j
    let cj := r - k; let c2 := cj > r
    c := c.push cj
    k := if c1 || c2 then 1 else 0
  return (c, k)

/-- One iteration of the loop, for `subLoop_eq` to fold over. -/
private def subStep (a b : Array Digit) (s : Array Digit × Digit) (j : Nat) : Array Digit × Digit :=
  let (c, k) := s
  let u_j := a.getD j 0
  let v_j := b.getD j 0
  let r := u_j - v_j
  let c1 := r > u_j
  let cj := r - k
  let c2 := cj > r
  (c.push cj, if c1 || c2 then 1 else 0)

/-- One iteration of the loop below, for `subInPlace_foldl` to fold over. -/
private def subInPlaceStep (b : Array Digit) (off : Nat) (s : Array Digit × Digit) (i : Nat) :
    Array Digit × Digit :=
  let (u, k) := s
  let u_i := u.getD (off + i) 0
  let v_i := b.getD i 0
  let r := u_i - v_i
  let c1 := r > u_i
  let ci := r - k
  let c2 := ci > r
  (u.set! (off + i) ci, if c1 || c2 then 1 else 0)

/-- One iteration of the loop below, for `mulInner_eq` to fold over. -/
private def mulInnerStep (a : Array Digit) (v_j : Digit) (j : Nat)
    (s : Array Digit × Digit) (i : Nat) : Array Digit × Digit :=
  let (c, k) := s
  let u_i := a.getD i 0
  let t : DoubleDigit :=
    u_i.toUInt64 * v_j.toUInt64 + (c.getD (i + j) 0).toUInt64 + k.toUInt64
  (c.set! (i + j) (lo t), hi t)

/-- `mul`'s inner loop with its length free, so that `mulInner_spec` can induct on it. -/
private def mulInner (a : Array Digit) (v_j : Digit) (j : Nat) (c : Array Digit) (lnga : Nat) :
    Array Digit × Digit := Id.run do
  let mut c := c
  let mut k : Digit := 0
  for i in List.range lnga do
    let u_i := a.getD i 0
    let t : DoubleDigit :=
      u_i.toUInt64 * v_j.toUInt64 + (c.getD (i + j) 0).toUInt64 + k.toUInt64
    c := c.set! (i + j) (lo t)
    k := hi t
  return (c, k)

/-- One iteration of `mul`'s outer loop, for `mulLoop_eq` to fold over. -/
private def mulOuterStep (a b : Array Digit) (c : Array Digit) (j : Nat) : Array Digit :=
  let v_j := b.getD j 0
  if v_j == 0 then
    c.set! (j + a.size) 0
  else
    let (c, k) := mulInner a v_j j c a.size
    c.set! (j + a.size) k

/-- The loop above with its length free, so that `mulLoop_spec` can induct on it. -/
private def mulLoop (a b : Array Digit) (m : Nat) : Array Digit := Id.run do
  let mut c := Array.replicate (a.size + b.size) 0
  for j in List.range m do
    c := mulOuterStep a b c j
  return c

/-- The loop above with its buffers and length free, so that `div1_spec` can induct on it. -/
private def div1Loop (denom : Digit) (hden : denom.toUInt64 ≠ 0) (u quot : Array Digit)
    (m : Nat) : Array Digit × Array Digit := Id.run do
  let mut s := (u, quot)
  for j in (List.range m).reverse do
    s := div1Step denom hden s (j+1)
  return s

/-- The loop above with its buffers and length free, so that `divN_spec` can induct on it. -/
private def divNLoop (denom : Array Digit) (hv : (denom.getD (denom.size - 1) 0).toUInt64 ≠ 0)
    (u quot : Array Digit) (m : Nat) : Array Digit × Array Digit := Id.run do
  let mut s := (u, quot)
  for j in (List.range m).reverse do
    s := divNStep denom hv s j
  return s


/-- `mpn_sub` is its loop at the length the C++ computes. -/
theorem sub_eq (a b : Array Digit) : sub a b = subLoop a b (max a.size b.size) := rfl

/-- The loop as the fold its proof inducts over. -/
theorem subLoop_eq (a b : Array Digit) (len : Nat) :
    subLoop a b len = (List.range len).foldl (fun s j => subStep a b s j) (#[], 0) := by
  simp [subLoop, subStep, Id.run]
  rfl

/-- The loop as the fold its proof inducts over. -/
theorem subInPlace_foldl (u b : Array Digit) (off len : Nat) :
    subInPlace u b off len
      = (List.range len).foldl (fun s i => subInPlaceStep b off s i) (u, 0) := by
  simp [subInPlace, subInPlaceStep, Id.run]
  rfl

private theorem subInPlace_succ (u b : Array Digit) (off len : Nat) :
    subInPlace u b off (len+1) = subInPlaceStep b off (subInPlace u b off len) len := by
  rw [subInPlace_foldl, subInPlace_foldl]
  simp [List.range_succ]

/-- The loop as the fold its proof inducts over. -/
theorem mulInner_eq (a : Array Digit) (v_j : Digit) (j : Nat) (c : Array Digit) (lnga : Nat) :
    mulInner a v_j j c lnga
      = (List.range lnga).foldl (fun s i => mulInnerStep a v_j j s i) (c, 0) := by
  simp [mulInner, mulInnerStep, Id.run]
  rfl

/-- The loop as the fold its proof inducts over. -/
theorem mulLoop_eq (a b : Array Digit) (m : Nat) :
    mulLoop a b m
      = (List.range m).foldl (fun c j => mulOuterStep a b c j)
          (Array.replicate (a.size + b.size) 0) := by
  simp [mulLoop, Id.run]
  rfl

/-- The loop as the map its proofs read digitwise. -/
theorem shiftRightDigits_eq (a : Array Digit) (d len : Nat) (hd : d < digitBits) :
    shiftRightDigits a d len hd = (Array.range len).map (fun i =>
      if h : d = 0 then a.getD i 0
      else CPP.shr (a.getD i 0) d hd |||
        (if i + 1 == len then 0
         else CPP.shl (lastBits (a.getD (i+1) 0) d (by omega)) (digitBits - d)
                (sub_digitBits_lt (by omega)))) := by
  unfold shiftRightDigits
  exact shiftLoop_eq (fun i =>
    if h : d = 0 then a.getD i 0
    else CPP.shr (a.getD i 0) d hd |||
      (if i + 1 == len then 0
       else CPP.shl (lastBits (a.getD (i+1) 0) d (by omega)) (digitBits - d)
              (sub_digitBits_lt (by omega)))) len

/-- The loop as the descending recursion its proof inducts over. -/
theorem div1Loop_eq (denom : Digit) (hden : denom.toUInt64 ≠ 0) (u quot : Array Digit)
    (m : Nat) :
    div1Loop denom hden u quot m
      = (List.range m).reverse.foldl (fun s j => div1Step denom hden s (j+1)) (u, quot) := by
  simp [div1Loop, Id.run]
  rfl

/-- One step of it, peeled off the top as `div_1` counts down. -/
theorem div1Loop_succ (denom : Digit) (hden : denom.toUInt64 ≠ 0) (u quot : Array Digit)
    (m : Nat) :
    div1Loop denom hden u quot (m+1)
      = div1Loop denom hden (div1Step denom hden (u, quot) (m+1)).1
          (div1Step denom hden (u, quot) (m+1)).2 m := by
  rw [div1Loop_eq, div1Loop_eq, List.range_succ, List.reverse_append]
  simp

/-- One iteration of it, peeled off the end. -/
theorem copyInto_succ (dst src : Array Digit) (j len : Nat) :
    copyInto dst src j (len+1) = (copyInto dst src j len).set! (j + len) (src.getD len 0) := by
  simp [copyInto, Id.run, List.range_succ]
  rfl

/-- `div_n` is its outer loop over a zeroed quotient buffer. -/
theorem divN_eq (numer denom : Array Digit) (hv : (denom.getD (denom.size - 1) 0).toUInt64 ≠ 0) :
    divN numer denom hv
      = divNLoop denom hv numer (Array.replicate (numer.size - denom.size) 0)
          (numer.size - denom.size) := rfl

/-- The loop as the descending recursion its proof inducts over. -/
theorem divNLoop_eq (denom : Array Digit) (hv : (denom.getD (denom.size - 1) 0).toUInt64 ≠ 0)
    (u quot : Array Digit) (m : Nat) :
    divNLoop denom hv u quot m
      = (List.range m).reverse.foldl (fun s j => divNStep denom hv s j) (u, quot) := by
  simp [divNLoop, Id.run]
  rfl

/-- One step of it, peeled off the top as `div_n` counts down. -/
theorem divNLoop_succ (denom : Array Digit) (hv : (denom.getD (denom.size - 1) 0).toUInt64 ≠ 0)
    (u quot : Array Digit) (m : Nat) :
    divNLoop denom hv u quot (m+1)
      = divNLoop denom hv (divNStep denom hv (u, quot) m).1
          (divNStep denom hv (u, quot) m).2 m := by
  rw [divNLoop_eq, divNLoop_eq, List.range_succ, List.reverse_append]
  simp


/-! ## Correctness of `mpn_add` -/

/-- The digit-level carry identity: `c[j] + carry * 2^32 = u_j + v_j + k`. -/
theorem addStep_digit (u v k : Digit) (hk : k.toNat ≤ 1) :
    ((u + v) + k).toNat
        + (if (u + v) < u || ((u + v) + k) < (u + v) then (1 : Digit) else 0).toNat * base
      = u.toNat + v.toNat + k.toNat := by
  have hsz : (UInt32.size : Nat) = 4294967296 := rfl
  have hu := UInt32.toNat_lt_size u
  have hv := UInt32.toNat_lt_size v
  simp only [base_eq]
  simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_add, hsz] at *
  split <;> rename_i h <;>
    simp only [Bool.or_eq_true, decide_eq_true_eq, UInt32.toNat_ofNat] at * <;> omega

private theorem add_combine {dc k p ua ub cj carry dna dnb B : Nat}
    (hval : dc + k * p = dna + dnb)
    (hstep : cj + carry * B = ua + ub + k) :
    dc + cj * p + carry * (p * B) = (dna + ua * p) + (dnb + ub * p) := by
  grind

theorem denote_trim (c : Array Digit) : denote (trim c) = denote c := by
  generalize h : trim c = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => fun c' => ULift.up c'.size
  | inv2 => ⇓ r => match r with
    | .inl c' => spred(⌜denote c' = denote c⌝)
    | .inr c' => spred(⌜denote c' = denote c⌝)
  all_goals (try (rw [denote_pop_of_back_zero])) <;> simp_all [Array.size_pop] <;> omega

/-- For a range loop split `range n = pref ++ cur :: suff`, the current index is the count so far. -/
private theorem range_split_index {n : Nat} {pref suff : List Nat} {cur : Nat}
    (h : List.range n = pref ++ cur :: suff) : cur = pref.length := by
  have hlen := congrArg List.length h
  simp only [List.length_range, List.length_append, List.length_cons] at hlen
  have h2 := congrArg (fun l => l[pref.length]?) h
  rw [List.getElem?_range (by omega), List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero] at h2
  exact (Option.some_inj.mp h2).symm

/-- `mpn_add` computes the sum. -/
theorem denote_add (a b : Array Digit) : denote (add a b) = denote a + denote b := by
  generalize h : add a b = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => ⇓ (xs, c, k) => spred(⌜c.size = xs.prefix.length ∧ k.toNat ≤ 1 ∧
      denote c + k.toNat * base ^ xs.prefix.length
        = denoteN a xs.prefix.length + denoteN b xs.prefix.length⌝)
  case vc1.step =>
    obtain ⟨hsz, hk, hval⟩ := ‹_ ∧ _ ∧ _›
    have hc := range_split_index ‹List.range _ = _ ++ _ :: _›
    subst hc
    refine ⟨by grind, by grind, ?_⟩
    rw [denote_push, hsz]
    simp only [List.length_append, List.length_cons, List.length_nil, denoteN, Nat.pow_succ]
    exact add_combine hval (addStep_digit _ _ _ hk)
  case vc3.post.success =>
    obtain ⟨hsz, hk, hval⟩ := ‹_ ∧ _ ∧ _›
    rw [denote_trim, denote_push, hsz, hval,
      denoteN_of_ge a (by simp; omega), denoteN_of_ge b (by simp; omega)]
  all_goals (first | rfl | (intros; simp_all))

/-! ## Correctness of `mpn_sub` -/

/-- The digit-level borrow identity: `c[j] + v_j + k = u_j + borrow * 2^32`. -/
theorem subStep_digit (u v k : Digit) (hk : k.toNat ≤ 1) :
    ((u - v) - k).toNat + v.toNat + k.toNat
      = u.toNat + (if (u - v) > u || ((u - v) - k) > (u - v) then (1 : Digit) else 0).toNat * base := by
  have hsz : (UInt32.size : Nat) = 4294967296 := rfl
  have hu := UInt32.toNat_lt_size u
  have hv := UInt32.toNat_lt_size v
  simp only [base_eq]
  simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub, hsz] at *
  split <;> rename_i h <;>
    simp only [Bool.or_eq_true, decide_eq_true_eq, UInt32.toNat_ofNat] at * <;> omega

theorem subStep_borrow_le (a b : Array Digit) (s : Array Digit × Digit) (j : Nat) :
    (subStep a b s j).2.toNat ≤ 1 := by
  simp only [subStep]; split <;> simp

private theorem sub_combine {dc k p ua ub cj borrow dna dnb B : Nat}
    (hval : dc + dnb = dna + k * p)
    (hstep : cj + ub + k = ua + borrow * B) :
    dc + cj * p + (dnb + ub * p) = dna + ua * p + borrow * (p * B) := by
  grind

/--
The loop invariant of `mpn_sub`: after `len` iterations the digits written so
far denote the difference of the first `len` digits of the two inputs, modulo
the outstanding borrow.
-/
theorem subLoop_spec (a b : Array Digit) (len : Nat) :
    (subLoop a b len).1.size = len ∧ (subLoop a b len).2.toNat ≤ 1 ∧
      denote (subLoop a b len).1 + denoteN b len
        = denoteN a len + (subLoop a b len).2.toNat * base ^ len := by
  induction len with
  | zero => exact ⟨rfl, Nat.zero_le _, rfl⟩
  | succ len ih =>
    obtain ⟨hsz, hk, hval⟩ := ih
    have hstep : subLoop a b (len+1) = subStep a b (subLoop a b len) len := by
      rw [subLoop_eq, subLoop_eq]
      simp [List.range_succ]
    rw [hstep]
    refine ⟨by simp [subStep, hsz], subStep_borrow_le .., ?_⟩
    have hd := subStep_digit (a.getD len 0) (b.getD len 0) (subLoop a b len).2 hk
    show denote ((subLoop a b len).1.push _) + _ = _
    rw [denote_push, hsz]
    exact sub_combine hval hd

/--
`mpn_sub` computes the difference: the result digits plus the subtrahend equal
the minuend, up to a borrow out of the top digit. In particular the borrow is
zero exactly when `b ≤ a`, and then the digits denote `a - b`.
-/
theorem denote_sub (a b : Array Digit) :
    denote (sub a b).1 + denote b
      = denote a + (sub a b).2.toNat * base ^ (max a.size b.size) := by
  obtain ⟨_, _, hval⟩ := subLoop_spec a b (max a.size b.size)
  simpa only [sub_eq, denoteN_of_ge a (Nat.le_max_left ..),
    denoteN_of_ge b (Nat.le_max_right ..)] using hval

/--
Running `mpn_sub` in place over `u[off..off+len)` gives what running it into a
separate buffer `w` gives, and touches nothing outside that window.

The window is what makes the aliasing safe: the digit the step at `i` reads has
not been written yet, because every earlier step wrote a strictly smaller index.
That is `hread` in the proof below.
-/
theorem subInPlace_spec (u b w : Array Digit) (off len : Nat)
    (hfits : off + len ≤ u.size)
    (hw : ∀ i, i < len → w.getD i 0 = u.getD (off + i) 0) :
    (subInPlace u b off len).1.size = u.size
    ∧ (subInPlace u b off len).2 = (subLoop w b len).2
    ∧ (∀ i, i < len →
        (subInPlace u b off len).1.getD (off + i) 0 = (subLoop w b len).1.getD i 0)
    ∧ (∀ i, ¬(off ≤ i ∧ i < off + len) →
        (subInPlace u b off len).1.getD i 0 = u.getD i 0) := by
  induction len with
  | zero => exact ⟨rfl, rfl, fun i h => absurd h (Nat.not_lt_zero i), fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨hsz, hk, hdig, hout⟩ := ih (by omega) (fun i hi => hw i (by omega))
    have hstep : subLoop w b (n+1) = subStep w b (subLoop w b n) n := by
      simp [subLoop_eq, List.range_succ]
    have hread : (subInPlace u b off n).1.getD (off + n) 0 = w.getD n 0 := by grind
    have hlensz : (subLoop w b n).1.size = n := (subLoop_spec w b n).1
    have hpush : ∀ (c : Array Digit) (d : Digit) (t : Nat), t = c.size →
        (c.push d).getD t 0 = d := by
      intro c d t h; subst h; exact getD_push_eq c d
    rw [subInPlace_succ, hstep]
    simp only [subInPlaceStep, subStep, hread, hk]
    refine ⟨by simp [hsz], ?_, ?_, ?_⟩
    · trivial
    · intro t ht
      rcases Nat.lt_or_ge t n with h | h
      · rw [getD_set!_ne _ _ _ _ (by omega), hdig t h, getD_push_lt _ _ (by omega)]
      · have htn : t = n := by omega
        subst htn
        rw [getD_set!_eq _ _ _ (by omega), hpush _ _ _ hlensz.symm]
    · intro t ht
      rw [getD_set!_ne _ _ _ _ (by omega), hout t (by omega)]

/-! ## Correctness of `mpn_mul` -/

/-- Splitting a 64-bit accumulator into its two digits loses nothing. -/
theorem lo_add_hi (t : DoubleDigit) : (lo t).toNat + (hi t).toNat * base = t.toNat := by
  have h := UInt64.toNat_lt_size t
  have hs : (UInt64.size : Nat) = 18446744073709551616 := rfl
  have h32 : (UInt64.ofNat digitBits).toNat % 64 = 32 := rfl
  simp only [lo, hi, CPP.shrD, CPP.shlD, base_eq, UInt64.toNat_toUInt32,
    UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hs, h32,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] at *
  omega

/--
The inner-loop accumulator `a[i] * v_j + c[i+j] + k` cannot overflow 64 bits: it
is at most `(2^32-1)^2 + 2*(2^32-1) = 2^64 - 1`. This is what makes the digit
identity exact rather than modular, and it is the one place where `mpn_mul`'s
correctness depends on `mpn_double_digit` being twice as wide as `mpn_digit`.
-/
theorem mulStep_toNat (x y z w : Digit) :
    (x.toUInt64 * y.toUInt64 + z.toUInt64 + w.toUInt64).toNat
      = x.toNat * y.toNat + z.toNat + w.toNat := by
  have hx := UInt32.toNat_lt_size x
  have hy := UInt32.toNat_lt_size y
  have hz := UInt32.toNat_lt_size z
  have hw := UInt32.toNat_lt_size w
  have hs : (UInt32.size : Nat) = 4294967296 := rfl
  have hb : x.toNat * y.toNat ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt32.toNat_toUInt64]
  omega

private theorem mulInner_combine {dc k p P Q ai v dc0 dna c0ij B lot hit : Nat}
    (hp : p = P * Q)
    (hval : dc + k * p = dc0 + dna * v * P)
    (hdig : lot + hit * B = ai * v + c0ij + k) :
    dc + lot * p + hit * (p * B) = dc0 + c0ij * p + (dna + ai * Q) * v * P := by grind

/--
The inner loop of `mpn_mul` adds `a * v_j` into `c` starting at digit `j`. It
touches only digits `j` up to `j + n` and leaves the overflow in its carry.
-/
theorem mulInner_spec (a : Array Digit) (v : Digit) (j : Nat) (c₀ : Array Digit) (n : Nat)
    (hn : j + n ≤ c₀.size) :
    (mulInner a v j c₀ n).1.size = c₀.size ∧
    (∀ idx, (idx < j ∨ j + n ≤ idx) →
      (mulInner a v j c₀ n).1.getD idx 0 = c₀.getD idx 0) ∧
    denoteN (mulInner a v j c₀ n).1 (j + n) + (mulInner a v j c₀ n).2.toNat * base ^ (j + n)
      = denoteN c₀ (j + n) + denoteN a n * v.toNat * base ^ j := by
  induction n with
  | zero => exact ⟨rfl, fun _ _ => rfl, by simp [mulInner, denoteN]⟩
  | succ n ih =>
    obtain ⟨hsz, huntouched, hval⟩ := ih (by omega)
    have hstep : mulInner a v j c₀ (n+1) = mulInnerStep a v j (mulInner a v j c₀ n) n := by
      rw [mulInner_eq, mulInner_eq]
      simp [List.range_succ]
    -- the digit this step reads has not been written yet
    have hread : (mulInner a v j c₀ n).1.getD (n + j) 0 = c₀.getD (n + j) 0 :=
      huntouched _ (Or.inr (by omega))
    have hlt : n + j < (mulInner a v j c₀ n).1.size := by omega
    rw [hstep]
    simp only [mulInnerStep, hread]
    refine ⟨by simp [hsz], ?_, ?_⟩
    · intro idx hidx
      rw [getD_set!_ne _ _ _ _ (by omega), huntouched idx (by omega)]
    · rw [show j + (n+1) = (n + j) + 1 by omega, denoteN_set!_succ _ _ _ hlt,
        show n + j = j + n by omega]
      exact mulInner_combine (Nat.pow_add base j n) hval
        (by rw [lo_add_hi, mulStep_toNat])

/--
The outer loop of `mpn_mul` accumulates `a * b` digit by digit: after `m`
iterations the buffer denotes `a` times the first `m` digits of `b`, and every
digit from `m + lnga` up is still zero.
-/
theorem mulLoop_spec (a b : Array Digit) (m : Nat) (hm : m ≤ b.size) :
    (mulLoop a b m).size = a.size + b.size ∧
    (∀ idx, m + a.size ≤ idx → (mulLoop a b m).getD idx 0 = 0) ∧
    denote (mulLoop a b m) = denote a * denoteN b m := by
  induction m with
  | zero =>
    refine ⟨by simp [mulLoop_eq], fun idx _ => ?_, ?_⟩
    · exact getD_replicate_zero _ _
    · rw [mulLoop_eq, List.range_zero, List.foldl_nil, denote_replicate_zero]; rfl
  | succ m ih =>
    obtain ⟨hsz, hzero, hval⟩ := ih (by omega)
    have hstep : mulLoop a b (m+1) = mulOuterStep a b (mulLoop a b m) m := by
      rw [mulLoop_eq, mulLoop_eq]
      simp [List.range_succ]
    have hb : denoteN b (m+1) = denoteN b m + (b.getD m 0).toNat * base ^ m := rfl
    have hfits : m + a.size < (mulLoop a b m).size := by omega
    rw [hstep]
    simp only [mulOuterStep]
    split <;> rename_i hv
    · -- `v_j == 0`: the digit about to be written is already zero
      have hv0 : (b.getD m 0).toNat = 0 := by
        simp only [beq_iff_eq] at hv; simp [hv]
      have hsame : ∀ i, i < (mulLoop a b m).size →
          ((mulLoop a b m).set! (m + a.size) 0).getD i 0 = (mulLoop a b m).getD i 0 := by
        intro i _
        by_cases h : i = m + a.size
        · subst h; rw [getD_set!_eq _ _ _ hfits, hzero _ (Nat.le_refl _)]
        · exact getD_set!_ne _ _ _ _ h
      refine ⟨by simp [hsz], ?_, ?_⟩
      · grind
      · rw [hb, hv0, Nat.zero_mul, Nat.add_zero, ← hval, denote,
          size_set!]
        exact denoteN_congr hsame
    · -- the general case: run the inner loop, then store its carry
      obtain ⟨hisz, hiunt, hival⟩ := mulInner_spec a (b.getD m 0) m (mulLoop a b m) a.size (by omega)
      have hcarry : m + a.size < (mulInner a (b.getD m 0) m (mulLoop a b m) a.size).1.size := by
        omega
      have hhigh : ∀ idx, (m + a.size) + 1 ≤ idx →
          (((mulInner a (b.getD m 0) m (mulLoop a b m) a.size).1).set! (m + a.size)
            (mulInner a (b.getD m 0) m (mulLoop a b m) a.size).2).getD idx 0 = 0 := by
        intro idx hidx
        rw [getD_set!_ne _ _ _ _ (by omega), hiunt idx (Or.inr (by omega)), hzero idx (by omega)]
      refine ⟨by rw [size_set!, hisz, hsz], ?_, ?_⟩
      · grind
      · rw [denote_of_high_zero _ (by rw [size_set!]; omega) hhigh,
          denoteN_set!_succ _ _ _ hcarry, hival,
          ← denote_of_high_zero (mulLoop a b m) (by rw [hsz]; omega)
            (fun idx h => hzero idx (by omega)),
          hval]
        show denote a * denoteN b m + denote a * (b.getD m 0).toNat * base ^ m
            = denote a * (denoteN b m + (b.getD m 0).toNat * base ^ m)
        rw [Nat.mul_add, Nat.mul_assoc]

/-- `List.finRange m` is `List.range m` once the bounds are forgotten. -/
private theorem map_val_finRange (m : Nat) : (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem <;> simp

/--
A fold over `Fin m` and a fold over `Nat` agree under any reading `r` of the state whose
steps agree. Used to read a `Vector` loop as the `Array` loop the specifications are about.
-/
private theorem foldl_hom {α β : Type} {m : Nat} (r : α → β)
    (f : α → Fin m → α) (g : β → Nat → β)
    (hfg : ∀ x i, r (f x i) = g (r x) i.val) (x : α) :
    r ((List.finRange m).foldl f x) = (List.range m).foldl g (r x) := by
  have h : ∀ (l : List (Fin m)) (x : α),
      r (l.foldl f x) = l.foldl (fun y i => g y i.val) (r x) := by
    intro l
    induction l with
    | nil => intro x; rfl
    | cons i l ih => intro x; simp [List.foldl_cons, ih, hfg]
  rw [h, ← map_val_finRange, List.foldl_map]

theorem mul_eq (a b : Array Digit) : mul a b = mulLoop a b b.size := by
  rw [mulLoop_eq]
  simp [mul, Id.run, ←apply_ite]
  refine foldl_hom Vector.toArray _ _ ?_ _
  intro v i
  -- The outer step: on `v_j == 0` both sides just write the carry at `j + a.size`; otherwise
  -- both run the inner loop. `mulInner_eq` keeps the right side's inner loop named as a
  -- `mulInnerStep` fold, so `foldl_hom` can bridge it to the `Vector` loop on the left.
  simp only [mulOuterStep, mulInner_eq]
  have key := foldl_hom (fun (s : Vector Digit (a.size + b.size) × Digit) => (s.1.toArray, s.2))
      (fun s (x : Fin a.size) =>
        (s.1.set (x.val + i.val)
            (lo (UInt32.toUInt64 a[x.val] * UInt32.toUInt64 b[i.val] +
                 UInt32.toUInt64 (s.1.getD (x.val + i.val) 0) + UInt32.toUInt64 s.2)) (by omega),
         hi (UInt32.toUInt64 a[x.val] * UInt32.toUInt64 b[i.val] +
             UInt32.toUInt64 (s.1.getD (x.val + i.val) 0) + UInt32.toUInt64 s.2)))
      (fun s i_1 => mulInnerStep a (b.getD i.val 0) i.val s i_1)
      (by intro x k; have := k.isLt; have := i.isLt
          simp [mulInnerStep, Vector.toArray_set, Array.setIfInBounds_def, Vector.getD]; omega) (v, 0)
  have hi2 := i.isLt
  have k1 : _ = _ := congrArg Prod.fst key
  have k2 : _ = _ := congrArg Prod.snd key
  dsimp only [Prod.fst, Prod.snd] at k1 k2
  rw [← k1, ← k2]
  simp only [apply_ite Vector.toArray, Vector.toArray_set, Array.set!_eq_setIfInBounds,
    Array.setIfInBounds_def, Vector.size_toArray]
  split <;> simp_all <;> omega

/-- `mpn_mul` computes the product. -/
theorem denote_mul (a b : Array Digit) : denote (mul a b) = denote a * denote b := by
  rw [mul_eq]; exact (mulLoop_spec a b b.size (Nat.le_refl _)).2.2

/-- `mpn_mul` writes exactly `lnga + lngb` digits, as its callers assume. -/
theorem size_mul (a b : Array Digit) : (mul a b).size = a.size + b.size := by
  rw [mul_eq]; exact (mulLoop_spec a b b.size (Nat.le_refl _)).1

/-!
## Towards `mpn_div`: Knuth's quotient-digit estimate

The arithmetic core of Knuth's Algorithm D, as pure `Nat` statements.

Digits are written relative to the divisor's length: with `n` divisor digits and
`k = n - 2`,

  v = (vtop * b + vsnd) * b^k + vrest      vrest < b^k,  vsnd < b,  1 ≤ vtop
  u = u2 * b^(k+1) + u3 * b^k + ulow       ulow < b^k,   u3 < b

so `u2` is the top two dividend digits and `u3` the next one down. `qhat` and
`rhat` are the trial quotient digit and its remainder, `u2 = qhat * vtop + rhat`
with `rhat < vtop`; step D3's test is `qhat * vsnd > b * rhat + u3`.
-/

namespace KnuthD


/-- Knuth 4.3.1 Theorem A: the trial quotient digit is never too small. -/
theorem le_qhat {u v P : Nat} (hP : 0 < P) (hv : 0 < v / P) :
    u / v ≤ (u / P) / (v / P) := by
  calc u / v ≤ u / (P * (v / P)) :=
        Nat.div_le_div_left (Nat.mul_div_le v P) (Nat.mul_pos hP hv)
    _ = u / P / (v / P) := (Nat.div_div_eq_div_mul u P (v / P)).symm

/--
Knuth 4.3.1 exercise 19: when step D3's test fires, the trial digit really is
too big, so decrementing it cannot undershoot the true quotient digit.
-/
theorem lt_of_test {b k vtop vsnd vrest u u2 u3 ulow qhat rhat : Nat}
    (hu : u = u2 * b ^ (k+1) + u3 * b ^ k + ulow) (hulow : ulow < b ^ k)
    (hu2 : u2 = qhat * vtop + rhat)
    (hfire : b * rhat + u3 < qhat * vsnd) :
    u < qhat * ((vtop * b + vsnd) * b ^ k + vrest) := by
  have hpow : b ^ (k+1) = b ^ k * b := Nat.pow_succ b k
  calc u = u2 * (b ^ k * b) + u3 * b ^ k + ulow := by rw [hu, hpow]
    _ < qhat * vtop * (b ^ k * b) + (b * rhat + u3 + 1) * b ^ k := by
        rw [hu2]; have : (qhat * vtop + rhat) * (b ^ k * b) + u3 * b ^ k + b ^ k
            = qhat * vtop * (b ^ k * b) + (b * rhat + u3 + 1) * b ^ k := by grind
        omega
    _ ≤ qhat * vtop * (b ^ k * b) + (qhat * vsnd) * b ^ k :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    _ = qhat * ((vtop * b + vsnd) * b ^ k) := by grind
    _ ≤ qhat * ((vtop * b + vsnd) * b ^ k + vrest) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

/--
The converse: when step D3's test fails, the trial digit is at most one too big,
which is exactly what makes the single add-back of step D6 enough. Only
`1 ≤ vtop` and `qhat < b` are needed, not the full normalization.
-/
theorem le_succ_of_not_test {b k vtop vsnd vrest u u2 u3 ulow qhat rhat : Nat}
    (hu : u = u2 * b ^ (k+1) + u3 * b ^ k + ulow)
    (hu2 : u2 = qhat * vtop + rhat)
    (hvrest : vrest < b ^ k) (hvtop : 1 ≤ vtop) (hqhat : qhat < b)
    (hfail : qhat * vsnd ≤ b * rhat + u3) :
    qhat * ((vtop * b + vsnd) * b ^ k + vrest)
      ≤ u + ((vtop * b + vsnd) * b ^ k + vrest) := by
  -- `qhat` times the divisor's leading part already fits under `u`
  have hmain : qhat * ((vtop * b + vsnd) * b ^ k) ≤ u := by
    calc qhat * ((vtop * b + vsnd) * b ^ k)
        = qhat * vtop * (b ^ k * b) + (qhat * vsnd) * b ^ k := by grind
      _ ≤ qhat * vtop * (b ^ k * b) + (b * rhat + u3) * b ^ k :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hfail) _
      _ = u2 * (b ^ k * b) + u3 * b ^ k := by grind
      _ ≤ u := by grind
  -- and the low part of the divisor that this ignores is itself below the divisor
  have hslack : qhat * vrest ≤ (vtop * b + vsnd) * b ^ k + vrest := by
    have h1 : qhat * vrest ≤ b * b ^ k := Nat.mul_le_mul (by omega) (by omega)
    have h2 : b * b ^ k ≤ (vtop * b + vsnd) * b ^ k := by
      refine Nat.mul_le_mul_right _ ?_
      calc b = 1 * b := (Nat.one_mul b).symm
        _ ≤ vtop * b := Nat.mul_le_mul_right b hvtop
        _ ≤ vtop * b + vsnd := Nat.le_add_right _ _
    exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_add_right _ _)
  grind

/-!
Restated against the divisor `v` and the true quotient digit `u / v`, which is
the form the loop proof consumes: after step D3 the trial digit is either exact
or one too big, and every decrement it performs is justified.
-/

/-- A trial digit whose test fires is strictly above the true quotient digit. -/
theorem div_lt_of_test {b k vtop vsnd vrest v u u2 u3 ulow qhat rhat : Nat}
    (hv : v = (vtop * b + vsnd) * b ^ k + vrest) (hvpos : 0 < v)
    (hu : u = u2 * b ^ (k+1) + u3 * b ^ k + ulow) (hulow : ulow < b ^ k)
    (hu2 : u2 = qhat * vtop + rhat)
    (hfire : b * rhat + u3 < qhat * vsnd) :
    u / v < qhat :=
  (Nat.div_lt_iff_lt_mul hvpos).mpr <| by
    have := lt_of_test (vrest := vrest) hu hulow hu2 hfire
    rw [hv]; omega

/-- A trial digit whose test fails is at most one above the true quotient digit. -/
theorem le_succ_div_of_not_test {b k vtop vsnd vrest v u u2 u3 ulow qhat rhat : Nat}
    (hv : v = (vtop * b + vsnd) * b ^ k + vrest) (hvpos : 0 < v)
    (hu : u = u2 * b ^ (k+1) + u3 * b ^ k + ulow)
    (hu2 : u2 = qhat * vtop + rhat)
    (hvrest : vrest < b ^ k) (hvtop : 1 ≤ vtop) (hqhat : qhat < b)
    (hfail : qhat * vsnd ≤ b * rhat + u3) :
    qhat ≤ u / v + 1 := by
  have hle : qhat * v ≤ u + v := by
    have := le_succ_of_not_test (vsnd := vsnd) hu hu2 hvrest hvtop hqhat hfail
    rw [hv]; omega
  rcases qhat with _ | m
  · exact Nat.zero_le _
  · have hm : m * v ≤ u := by
      have : (m+1) * v = m * v + v := by grind
      omega
    have := (Nat.le_div_iff_mul_le hvpos).mpr hm
    omega

end KnuthD

/-! ## Correctness of `div_normalize`'s shift -/

/-- The bits that digit `j-1` sends up into digit `j` under a left shift by `d`. -/
private def shiftCarry (a : Array Digit) (d j : Nat) : Nat :=
  if j = 0 then 0 else (a.getD (j-1) 0).toNat / 2 ^ (digitBits - d)

private theorem shiftCarry_eq (a : Array Digit) {d j : Nat} (hd0 : 0 < d) (hd : d < digitBits)
    (hj : j ≠ 0) : shiftCarry a d j = (a.getD (j-1) 0).toNat * 2 ^ d / base := by
  simp only [shiftCarry, hj, ite_false, digitBits_eq] at *
  have hb : base = 2 ^ (32 - d) * 2 ^ d := by
    rw [← Nat.pow_add, show 32 - d + d = 32 by omega]; rfl
  rw [hb, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos d)]

private theorem shift_combine {Oj C C' P Dj A B T : Nat}
    (hih : Oj + C * P = Dj * T)
    (hdm : A * T % B + B * (A * T / B) = A * T)
    (hC' : C' = A * T / B) :
    Oj + (A * T % B + C) * P + C' * (P * B) = (Dj + A * P) * T := by grind

/-- The shifted digits denote `2^d` times the original, modulo what falls off the top. -/
theorem denoteN_shiftLeftDigits (a : Array Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits)
    {len j : Nat} (hj : j ≤ len) :
    denoteN (shiftLeftDigits a d len hd) j + shiftCarry a d j * base ^ j = denoteN a j * 2 ^ d := by
  induction j with
  | zero => simp [denoteN, shiftCarry]
  | succ j ih =>
    have hdigit : ((shiftLeftDigits a d len hd).getD j 0).toNat
        = (a.getD j 0).toNat * 2 ^ d % base + shiftCarry a d j := by
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        rw [getD_shiftLeftDigits_head a hd0 hd (by omega), toNat_shl _ hd]
        simp [shiftCarry]
      · rw [getD_shiftLeftDigits_tail a hd0 hd (by omega) (by omega), toNat_shl_or_shr _ _ hd0 hd]
        simp only [shiftCarry, Nat.ne_of_gt hj0, ite_false]
    have hC' : shiftCarry a d (j+1) = (a.getD j 0).toNat * 2 ^ d / base := by
      simp [shiftCarry_eq a hd0 hd (Nat.succ_ne_zero j)]
    have hdm := Nat.div_add_mod ((a.getD j 0).toNat * 2 ^ d) base
    rw [denoteN, hdigit]
    exact shift_combine (ih (by omega)) (by omega) hC'

/--
A left shift by `d` bits multiplies the denotation by `2^d`, provided the result
still fits in `len` digits. `div_normalize` gives the numerator one extra digit
for exactly this reason, and chooses `d` so the denominator does not overflow.
-/
theorem denote_shiftLeftDigits (a : Array Digit) {d : Nat} (hd : d < digitBits)
    {len : Nat} (hlen : a.size ≤ len) (hfit : denote a * 2 ^ d < base ^ len) :
    denote (shiftLeftDigits a d len hd) = denote a * 2 ^ d := by
  have hout : denote (shiftLeftDigits a d len hd) = denoteN (shiftLeftDigits a d len hd) len := by
    rw [denote, size_shiftLeftDigits]
  have ha : denoteN a len = denote a := denoteN_of_ge a hlen
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    have hcongr : ∀ i, i < len → (shiftLeftDigits a 0 len hd).getD i 0 = a.getD i 0 := by
      intro i hi; exact getD_shiftLeftDigits_zero a len i hi hd
    simp [hout, denoteN_congr hcongr, ha]
  · have hmain := denoteN_shiftLeftDigits a hd0 hd (Nat.le_refl len)
    rw [ha] at hmain
    -- nothing can fall off the top, so the carry out of the last digit is zero
    have hzero : shiftCarry a d len = 0 := by
      rcases Nat.eq_zero_or_pos (shiftCarry a d len) with h | h
      · exact h
      · exact absurd hmain (by
          have : base ^ len ≤ shiftCarry a d len * base ^ len := Nat.le_mul_of_pos_left _ h
          omega)
    grind

/-! ## Correctness of `div_normalize` -/

/--
`div_normalize`. The numerator gains a digit and both operands are multiplied by
`2^d`, where `d` is chosen so the leading denominator digit ends up with its top
bit set, which is what Knuth's Algorithm D assumes of its divisor.
-/
theorem divNormalize_spec (numer denom : Array Digit) (hnum : 0 < numer.size)
    (hden : 0 < denom.size) (htop : 0 < (denom.getD (denom.size - 1) 0).toNat) :
    (divNormalize numer denom).2.1.size = numer.size + 1 ∧
    (divNormalize numer denom).2.2.size = denom.size ∧
    denote (divNormalize numer denom).2.1 = denote numer * 2 ^ (divNormalize numer denom).1.val ∧
    denote (divNormalize numer denom).2.2 = denote denom * 2 ^ (divNormalize numer denom).1.val ∧
    2147483648 ≤ ((divNormalize numer denom).2.2.getD (denom.size - 1) 0).toNat := by
  obtain ⟨hlo, hhi⟩ := leadingZeros_spec (denom.getD (denom.size - 1) 0) htop
  have hdlt := (leadingZeros (denom.getD (denom.size - 1) 0)).isLt
  rw [divNormalize_eq numer denom hnum hden]
  dsimp only
  refine ⟨size_shiftLeftDigits _ _ _ _, size_shiftLeftDigits _ _ _ _, ?_, ?_, ?_⟩
  · -- the numerator has a spare digit, so `2^d < base` is room enough
    refine denote_shiftLeftDigits numer hdlt (by omega) ?_
    have h1 : denote numer < base ^ numer.size := denoteN_lt numer numer.size
    have h2 : (2:Nat) ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val ≤ base := by
      calc (2:Nat) ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val ≤ 2 ^ 32 :=
            Nat.pow_le_pow_right (by omega) (by simp only [digitBits_eq] at hdlt; omega)
        _ = base := rfl
    calc denote numer * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val
        < base ^ numer.size * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
      _ ≤ base ^ numer.size * base := Nat.mul_le_mul_left _ h2
  · -- the denominator has no spare digit; `d` was chosen so it does not need one
    refine denote_shiftLeftDigits denom hdlt (Nat.le_refl _) ?_
    have hsplit : denote denom
        < ((denom.getD (denom.size - 1) 0).toNat + 1) * base ^ (denom.size - 1) := by
      have hlow : denoteN denom (denom.size - 1) < base ^ (denom.size - 1) :=
        denoteN_lt denom (denom.size - 1)
      have hden' : denote denom = denoteN denom (denom.size - 1)
          + (denom.getD (denom.size - 1) 0).toNat * base ^ (denom.size - 1) := by
        obtain ⟨m, hm⟩ : ∃ m, denom.size = m + 1 := ⟨denom.size - 1, by omega⟩
        rw [denote, hm]
        rfl
      rw [Nat.add_mul]
      omega
    -- `t * 2^d < base` forces `(t + 1) * 2^d ≤ base`
    have hstep : ((denom.getD (denom.size - 1) 0).toNat + 1)
        * 2 ^ ((leadingZeros (denom.getD (denom.size - 1) 0)).val) ≤ base := by
      have hd32 : (leadingZeros (denom.getD (denom.size - 1) 0)).val < 32 := by
        simp only [digitBits_eq] at hdlt; omega
      have hb : base = 2 ^ (32 - (leadingZeros (denom.getD (denom.size - 1) 0)).val)
          * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val := by
        rw [← Nat.pow_add, show 32 - (leadingZeros (denom.getD (denom.size - 1) 0)).val
          + (leadingZeros (denom.getD (denom.size - 1) 0)).val = 32 by omega]; rfl
      have hlt : (denom.getD (denom.size - 1) 0).toNat
          < 2 ^ (32 - (leadingZeros (denom.getD (denom.size - 1) 0)).val) := by
        refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val) ?_
        rw [← hb]; exact hhi
      calc ((denom.getD (denom.size - 1) 0).toNat + 1)
            * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val
          ≤ 2 ^ (32 - (leadingZeros (denom.getD (denom.size - 1) 0)).val)
            * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val :=
            Nat.mul_le_mul_right _ (by omega)
        _ = base := hb.symm
    calc denote denom * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val
        < ((denom.getD (denom.size - 1) 0).toNat + 1) * base ^ (denom.size - 1)
            * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)).val :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hsplit
      _ = (((denom.getD (denom.size - 1) 0).toNat + 1)
            * 2 ^ ((leadingZeros (denom.getD (denom.size - 1) 0)).val)) * base ^ (denom.size - 1) := by
          grind
      _ ≤ base * base ^ (denom.size - 1) := Nat.mul_le_mul_right _ hstep
      _ = base ^ denom.size := by
          rw [Nat.mul_comm, ← Nat.pow_succ]
          congr 1
          omega
  · -- the shifted leading digit keeps the bits `leadingZeros` put in place
    have hle := le_getD_shiftLeftDigits denom (d := (leadingZeros (denom.getD (denom.size - 1) 0)).val)
      (len := denom.size) (j := denom.size - 1) hdlt (by omega)
    rw [Nat.mod_eq_of_lt hhi] at hle
    omega

/-! ## Correctness of `div_unnormalize` -/

theorem toNat_lastBits (x : Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits) :
    (lastBits x d hd0).toNat = x.toNat % 2 ^ d := by
  have hd' : d < 32 := by simpa [digitBits_eq] using hd
  simp only [lastBits, CPP.shr, CPP.shl]
  rw [toNat_shr _ (by simp [digitBits_eq]; omega), toNat_shl _ (by simp [digitBits_eq]; omega)]
  simp only [digitBits_eq]
  have hb : base = 2 ^ d * 2 ^ (32 - d) := by
    rw [← Nat.pow_add, show d + (32 - d) = 32 by omega]; rfl
  rw [hb, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos (32 - d))]

/--
Recombining two adjacent digits under a right shift by `d`: as with the left
shift, the `|` cannot carry, since `a[i] >> d` is below `2^(32-d)` and the bits
arriving from above are a multiple of it.
-/
theorem toNat_shr_or_shl (x y : Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits) :
    ((x >>> (UInt32.ofNat d)) ||| (lastBits y d hd0 <<< (UInt32.ofNat (digitBits - d)))).toNat
      = x.toNat / 2 ^ d + y.toNat % 2 ^ d * 2 ^ (digitBits - d) := by
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
  have hlow : x.toNat / 2 ^ d < 2 ^ (digitBits - d) := by
    simp only [digitBits_eq] at hd hd0 ⊢
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show d + (32 - d) = 32 by omega]
    exact hx
  have hhigh : (lastBits y d hd0 <<< (UInt32.ofNat (digitBits - d))).toNat
      = (y.toNat % 2 ^ d) <<< (digitBits - d) := by
    rw [toNat_shl _ (by simp only [digitBits_eq] at hd0 ⊢; omega), toNat_lastBits y hd0 hd,
      Nat.shiftLeft_eq]
    refine Nat.mod_eq_of_lt ?_
    simp only [digitBits_eq] at hd hd0 ⊢
    calc y.toNat % 2 ^ d * 2 ^ (32 - d) < 2 ^ d * 2 ^ (32 - d) :=
          Nat.mul_lt_mul_right (Nat.two_pow_pos _) |>.mpr (Nat.mod_lt _ (Nat.two_pow_pos d))
      _ = base := by rw [← Nat.pow_add, show d + (32 - d) = 32 by omega]; rfl
  rw [UInt32.toNat_or, hhigh, toNat_shr _ (by simp only [digitBits_eq] at hd ⊢; omega),
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlow, Nat.shiftLeft_eq, Nat.add_comm]

private theorem getD_shiftRightDigits_zero (a : Array Digit) (len j : Nat) (hj : j < len)
    (hd : 0 < digitBits) : (shiftRightDigits a 0 len hd).getD j 0 = a.getD j 0 := by
  simp [shiftRightDigits_eq, hj]

private theorem getD_shiftRightDigits_last (a : Array Digit) {d len : Nat} (hd0 : 0 < d)
    (hd : d < digitBits) (hlen : 0 < len) :
    (shiftRightDigits a d len hd).getD (len - 1) 0 = a.getD (len - 1) 0 >>> UInt32.ofNat d := by
  simp [shiftRightDigits_eq, Nat.ne_of_gt hd0, show len - 1 < len by omega,
    show len - 1 + 1 = len by omega]

private theorem getD_shiftRightDigits_mid (a : Array Digit) {d len j : Nat} (hd0 : 0 < d)
    (hd : d < digitBits) (hj : j < len) (hj' : j + 1 ≠ len) :
    (shiftRightDigits a d len hd).getD j 0
      = (a.getD j 0 >>> UInt32.ofNat d) |||
        (lastBits (a.getD (j+1) 0) d hd0 <<< UInt32.ofNat (digitBits - d)) := by
  simp [shiftRightDigits_eq, Nat.ne_of_gt hd0, hj, hj']

private theorem shiftRight_combine {Rj rj xj xj1 P T U B Nj lo0 : Nat}
    (hB : U * T = B)
    (hih : Rj * T + lo0 = Nj + xj % T * P)
    (hrj : rj = xj / T + xj1 % T * U)
    (hdm : xj % T + T * (xj / T) = xj) :
    (Rj + rj * P) * T + lo0 = Nj + xj * P + xj1 % T * (P * B) := by grind

theorem size_shiftRightDigits (a : Array Digit) (d len : Nat) (hd : d < digitBits) :
    (shiftRightDigits a d len hd).size = len := by simp [shiftRightDigits_eq]

/--
The loop invariant of the right shift: the digits written so far, scaled back up
by `2^d` and given the bits that fell off the bottom, account for the digits of
`a` they were built from, up to the bits digit `j` still owes downward.
-/
theorem denoteN_shiftRightDigits (a : Array Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits)
    {len j : Nat} (hj : j < len) :
    denoteN (shiftRightDigits a d len hd) j * 2 ^ d + (a.getD 0 0).toNat % 2 ^ d
      = denoteN a j + (a.getD j 0).toNat % 2 ^ d * base ^ j := by
  induction j with
  | zero => simp [denoteN]
  | succ j ih =>
    have hmid : ((shiftRightDigits a d len hd).getD j 0).toNat
        = (a.getD j 0).toNat / 2 ^ d + (a.getD (j+1) 0).toNat % 2 ^ d * 2 ^ (digitBits - d) := by
      rw [getD_shiftRightDigits_mid a hd0 hd (by omega) (by omega), toNat_shr_or_shl _ _ hd0 hd]
    have hB : 2 ^ (digitBits - d) * 2 ^ d = base := by
      simp only [digitBits_eq] at hd hd0 ⊢
      rw [← Nat.pow_add, show 32 - d + d = 32 by omega]; rfl
    have hdm := Nat.div_add_mod (a.getD j 0).toNat (2 ^ d)
    exact shiftRight_combine hB (ih (by omega)) hmid (by omega)

/--
`div_unnormalize` divides the denotation by `2^d`, undoing what
`div_normalize` did to the numerator and leaving the true remainder.
-/
theorem denote_shiftRightDigits (a : Array Digit) {d : Nat} (hd : d < digitBits) {len : Nat}
    (hlen : 0 < len) :
    denote (shiftRightDigits a d len hd) = denoteN a len / 2 ^ d := by
  have hsize : (shiftRightDigits a d len hd).size = len := size_shiftRightDigits _ _ _ hd
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    have hcongr : ∀ i, i < len → (shiftRightDigits a 0 len hd).getD i 0 = a.getD i 0 :=
      fun i hi => getD_shiftRightDigits_zero a len i hi hd
    simp [denote, hsize, denoteN_congr hcongr]
  · have hlast : ((shiftRightDigits a d len hd).getD (len-1) 0).toNat
        = (a.getD (len-1) 0).toNat / 2 ^ d := by
      rw [getD_shiftRightDigits_last a hd0 hd hlen, toNat_shr _ hd]
    have hinv := denoteN_shiftRightDigits a hd0 hd (len := len) (j := len - 1) (by omega)
    have hdm := Nat.div_add_mod (a.getD (len-1) 0).toNat (2 ^ d)
    have hlo : (a.getD 0 0).toNat % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
    -- fold the last digit in, which owes nothing downward
    have hfull : denote (shiftRightDigits a d len hd) * 2 ^ d + (a.getD 0 0).toNat % 2 ^ d
        = denoteN a len := by
      have hexp : denote (shiftRightDigits a d len hd)
          = denoteN (shiftRightDigits a d len hd) (len-1)
            + ((shiftRightDigits a d len hd).getD (len-1) 0).toNat * base ^ (len-1) := by
        obtain ⟨m, hm⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
        rw [denote, hsize, hm]; rfl
      have hexpa : denoteN a len
          = denoteN a (len-1) + (a.getD (len-1) 0).toNat * base ^ (len-1) := by
        obtain ⟨m, hm⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
        rw [hm]; rfl
      rw [hexp, hlast, Nat.add_mul]
      have : (a.getD (len-1) 0).toNat / 2 ^ d * base ^ (len-1) * 2 ^ d
          + (a.getD (len-1) 0).toNat % 2 ^ d * base ^ (len-1)
          = (a.getD (len-1) 0).toNat * base ^ (len-1) := by grind
      omega
    rw [← hfull, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos d),
      Nat.div_eq_of_lt hlo, Nat.add_zero]

/-! ## Correctness of `div_1` -/

private theorem lo_of_lt (x : DoubleDigit) (h : x.toNat < base) : (lo x).toNat = x.toNat := by
  have hla := lo_add_hi x
  rcases Nat.eq_zero_or_pos (hi x).toNat with h0 | h0
  · grind
  · exact absurd hla (by have : base ≤ (hi x).toNat * base := Nat.le_mul_of_pos_left _ h0; omega)

private theorem hi_of_lt (x : DoubleDigit) (h : x.toNat < base) : hi x = 0 := by
  have hla := lo_add_hi x
  have : (hi x).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (hi x).toNat with h0 | h0
    · exact h0
    · exact absurd hla (by have : base ≤ (hi x).toNat * base := Nat.le_mul_of_pos_left _ h0; omega)
  exact UInt32.toNat_inj.mp (by rw [this]; rfl)

/-- The two-digit window `(u[j] << 32) | u[j-1]` that `div_1` and `div_n` divide. -/
private theorem toNat_window (x y : Digit) :
    ((x.toUInt64 <<< 32) ||| y.toUInt64).toNat = x.toNat * base + y.toNat := by
  have hx : x.toNat < 4294967296 := x.toNat_lt_size
  have hy : y.toNat < 4294967296 := y.toNat_lt_size
  have hshl : (x.toUInt64 <<< 32).toNat = x.toNat <<< 32 := by
    refine Nat.mod_eq_of_lt ?_
    rw [Nat.shiftLeft_eq]
    calc x.toNat * 2 ^ 32 < 4294967296 * 2 ^ 32 :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos 32)).mpr hx
      _ = 2 ^ 64 := rfl
  rw [UInt64.toNat_or, hshl,
    ← Nat.shiftLeft_add_eq_or_of_lt (i := 32) (by exact hy), Nat.shiftLeft_eq]
  rfl

/-- The numeric core of a `div_1` step: an exact division whose add-back is dead. -/
private theorem u64_divmod (T d : DoubleDigit) (hd : 0 < d.toNat) (hdb : d.toNat < base)
    (hTlt : T.toNat < d.toNat * base) :
    (lo (T / d)).toNat = T.toNat / d.toNat ∧
    (lo (T - (T / d) * d)).toNat = T.toNat % d.toNat ∧
    hi (T - (T / d) * d) = 0 ∧
    ¬ ((T - (T / d) * d) > T) := by
  have hT64 : T.toNat < 2 ^ 64 := T.toNat_lt_size
  have hqlt : T.toNat / d.toNat < base :=
    Nat.div_lt_of_lt_mul hTlt
  have hq : (T / d).toNat = T.toNat / d.toNat := UInt64.toNat_div ..
  have hprod : ((T / d) * d).toNat = T.toNat / d.toNat * d.toNat := by
    have hle : T.toNat / d.toNat * d.toNat ≤ T.toNat := Nat.div_mul_le_self _ _
    rw [UInt64.toNat_mul, hq]
    exact Nat.mod_eq_of_lt (by omega)
  have hms : (T - (T / d) * d).toNat = T.toNat % d.toNat := by
    have hdm := Nat.div_add_mod' T.toNat d.toNat
    rw [UInt64.toNat_sub, hprod]
    omega
  have hmslt : (T - (T / d) * d).toNat < base := by
    rw [hms]; exact Nat.lt_trans (Nat.mod_lt _ hd) hdb
  refine ⟨by rw [lo_of_lt _ (by rw [hq]; omega), hq], by rw [lo_of_lt _ hmslt, hms],
    hi_of_lt _ hmslt, ?_⟩
  simp only [UInt64.lt_iff_toNat_lt, hms, Nat.not_lt]
  exact Nat.mod_le _ _

/-- Each `div_1` step divides its two-digit window exactly. -/
private theorem div1Step_eq (denom : Digit) (u quot : Array Digit) (j : Nat)
    (hd : 0 < denom.toNat) (hlt : (u.getD (j+1) 0).toNat < denom.toNat) :
    ∃ q r : Digit,
      q.toNat = ((u.getD (j+1) 0).toNat * base + (u.getD j 0).toNat) / denom.toNat ∧
      r.toNat = ((u.getD (j+1) 0).toNat * base + (u.getD j 0).toNat) % denom.toNat ∧
      div1Step denom (toUInt64_ne_zero hd) (u, quot) (j+1) = ((u.set! j r).set! (j+1) 0, quot.set! j q) := by
  obtain ⟨W, hW⟩ : ∃ W : DoubleDigit,
      W = ((u.getD (j+1) 0).toUInt64 <<< 32) ||| (u.getD j 0).toUInt64 := ⟨_, rfl⟩
  have hlow : (u.getD j 0).toNat < base := (u.getD j 0).toNat_lt_size
  have hd64 : 0 < denom.toUInt64.toNat := by rw [UInt32.toNat_toUInt64]; exact hd
  have hdb64 : denom.toUInt64.toNat < base := by
    exact denom.toNat_lt_size
  have hWn : W.toNat = (u.getD (j+1) 0).toNat * base + (u.getD j 0).toNat := by
    rw [hW, toNat_window]
  have hTlt : W.toNat < denom.toUInt64.toNat * base := by
    rw [hWn, UInt32.toNat_toUInt64]
    calc (u.getD (j+1) 0).toNat * base + (u.getD j 0).toNat
        < ((u.getD (j+1) 0).toNat + 1) * base := by grind
      _ ≤ denom.toNat * base := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨hq, hr, hhi, hnb⟩ := u64_divmod W denom.toUInt64 hd64 hdb64 hTlt
  rw [UInt32.toNat_toUInt64] at hq hr
  refine ⟨lo (W / denom.toUInt64), lo (W - (W / denom.toUInt64) * denom.toUInt64), ?_, ?_, ?_⟩
  · rw [hq, hWn]
  · rw [hr, hWn]
  · have hnz : denom.toUInt64 ≠ 0 := toUInt64_ne_zero hd
    simp only [div1Step, Nat.add_sub_cancel, ← hW]
    simp [hhi, hnb]

private theorem denoteN_set!_of_zero (c : Array Digit) (idx : Nat) (d : Digit)
    (hidx : idx < c.size) (hz : c.getD idx 0 = 0) :
    ∀ n, idx < n → denoteN (c.set! idx d) n = denoteN c n + d.toNat * base ^ idx := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro hn
    rcases Nat.lt_or_ge idx n with h | h
    · rw [denoteN, denoteN, getD_set!_ne c idx n d (by omega)]
      omega
    · have hidxn : idx = n := by omega
      subst hidxn
      rw [denoteN, denoteN, denoteN_set!_of_le c idx d (Nat.le_refl _),
        getD_set!_eq c idx d hidx, hz]
      simp

theorem denote_set!_of_zero (c : Array Digit) (idx : Nat) (d : Digit)
    (hidx : idx < c.size) (hz : c.getD idx 0 = 0) :
    denote (c.set! idx d) = denote c + d.toNat * base ^ idx := by
  rw [denote, size_set!]
  exact denoteN_set!_of_zero c idx d hidx hz c.size (by omega)

private theorem div1_combine {Q D Nj uj1 nj q r P B N : Nat}
    (hqr : q * D + r = uj1 * B + nj)
    (hval : Q * D + (Nj + nj * P) + uj1 * (P * B) = N) :
    (Q + q * P) * D + Nj + r * P = N := by
  grind

/--
The loop invariant of `div_1`: the quotient digits written so far, times the
divisor, plus the numerator digits not yet consumed and the running one-digit
remainder, account for the whole numerator.
-/
private theorem norm_top_ne_zero {denom : Array Digit} {k : Nat} (hk : denom.size = k + 2)
    (hnorm : base ≤ 2 * (denom.getD (k+1) 0).toNat) :
    (denom.getD (denom.size - 1) 0).toUInt64 ≠ 0 := by
  rw [hk, show k + 2 - 1 = k + 1 from rfl]
  exact toUInt64_ne_zero (by simp only [base_eq] at hnorm; omega)

theorem div1Loop_spec (denom : Digit) (numer : Array Digit) (hd : 0 < denom.toNat) :
    ∀ (j : Nat) (u quot : Array Digit), u.size = numer.size → quot.size = numer.size - 1 →
      j < numer.size →
      (∀ i, i < j → u.getD i 0 = numer.getD i 0) →
      (∀ i, i < j → quot.getD i 0 = 0) →
      (u.getD j 0).toNat < denom.toNat →
      denote quot * denom.toNat + denoteN numer j + (u.getD j 0).toNat * base ^ j
        = denoteN numer numer.size →
      ((div1Loop denom (toUInt64_ne_zero hd) u quot j).1.getD 0 0).toNat < denom.toNat ∧
      (div1Loop denom (toUInt64_ne_zero hd) u quot j).2.size = numer.size - 1 ∧
      denote (div1Loop denom (toUInt64_ne_zero hd) u quot j).2 * denom.toNat
          + ((div1Loop denom (toUInt64_ne_zero hd) u quot j).1.getD 0 0).toNat = denoteN numer numer.size := by
  intro j
  induction j with
  | zero =>
    intro u quot hu hq _ _ _ hrem hval
    refine ⟨hrem, hq, ?_⟩
    simpa [div1Loop, denoteN] using hval
  | succ j ih =>
    intro u quot hu hq hjn hlow hqz hrem hval
    obtain ⟨q, r, hqv, hrv, hstep⟩ := div1Step_eq denom u quot j hd hrem
    have hjq : j < quot.size := by omega
    have hju : j < u.size := by omega
    have hnj : u.getD j 0 = numer.getD j 0 := hlow j (by omega)
    have hset : (u.set! j r).getD j 0 = r := getD_set!_eq u j r hju
    rw [div1Loop_succ, hstep]
    refine ih ((u.set! j r).set! (j+1) 0) (quot.set! j q) (by simp [hu]) (by simp [hq])
      (by omega) ?_ ?_ ?_ ?_
    · intro i hi
      rw [getD_set!_ne _ _ _ _ (by omega), getD_set!_ne _ _ _ _ (by omega)]
      exact hlow i (by omega)
    · intro i hi
      rw [getD_set!_ne _ _ _ _ (by omega)]
      exact hqz i (by omega)
    · rw [getD_set!_ne _ _ _ _ (by omega), hset, hrv]
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_refl _)
    · rw [getD_set!_ne _ _ _ _ (by omega), hset,
        denote_set!_of_zero quot j q hjq (hqz j (by omega)), hrv]
      have hqr : q.toNat * denom.toNat + r.toNat
          = (u.getD (j+1) 0).toNat * base + (numer.getD j 0).toNat := by
        rw [hqv, hrv, hnj]
        exact Nat.div_add_mod' _ _
      have hvalj : denote quot * denom.toNat
          + (denoteN numer j + (numer.getD j 0).toNat * base ^ j)
          + (u.getD (j+1) 0).toNat * (base ^ j * base) = denoteN numer numer.size := by
        exact hval
      rw [← hrv]
      exact div1_combine hqr hvalj

/--
`div_1` computes a quotient and a one-digit remainder, given that the leading
numerator digit is already below the divisor, which is what normalization
arranges. Its `lean_unreachable()` for `q_hat >= BASE` is unreachable for the
same reason.
-/
theorem div1_spec (numer : Array Digit) (denom : Digit) (hd : 0 < denom.toNat)
    (hn : 0 < numer.size)
    (htop : (numer.getD (numer.size - 1) 0).toNat < denom.toNat) :
    ((div1 numer denom (toUInt64_ne_zero hd)).1.getD 0 0).toNat < denom.toNat ∧
    (div1 numer denom (toUInt64_ne_zero hd)).2.size = numer.size - 1 ∧
    denote (div1 numer denom (toUInt64_ne_zero hd)).2 * denom.toNat + ((div1 numer denom (toUInt64_ne_zero hd)).1.getD 0 0).toNat
      = denoteN numer numer.size := by
  refine div1Loop_spec denom numer hd (numer.size - 1) numer _ rfl (by simp) (by omega)
    (fun _ _ => rfl) (fun i _ => getD_replicate_zero _ _) htop ?_
  rw [denote_replicate_zero, Nat.zero_mul, Nat.zero_add]
  obtain ⟨m, hm⟩ : ∃ m, numer.size = m + 1 := ⟨numer.size - 1, by omega⟩
  rw [hm]
  rfl

/-! ## Correctness of step D3 -/

/-- Normalization keeps the trial digit within one of a single digit. -/
private theorem q_le_of_inv {q r vtop u2 : Nat} (hinv : u2 = q * vtop + r)
    (hu2 : u2 ≤ vtop * base + (base - 1)) (hnorm : base ≤ 2 * vtop) : q ≤ base + 1 := by
  rcases Nat.lt_or_ge q (base + 2) with h | h
  · omega
  · exfalso
    have h1 : (base + 2) * vtop ≤ q * vtop := Nat.mul_le_mul_right _ h
    simp only [base_eq] at *
    omega

/-- Step D3's test, read arithmetically. -/
private theorem recheck_test_iff (dn2 nu : Digit) (q r : DoubleDigit)
    (hq : q.toNat ≤ base + 1) (hr : r.toNat < base) :
    ((q >>> 32 != 0 || q * dn2.toUInt64 > ((r <<< 32) + nu.toUInt64)) = true)
      = (base ≤ q.toNat ∨ base * r.toNat + nu.toNat < q.toNat * dn2.toNat) := by
  have hd2 : dn2.toNat < base := dn2.toNat_lt_size
  have hnu : nu.toNat < base := nu.toNat_lt_size
  have hshr : (q >>> 32).toNat = q.toNat / 4294967296 := by
    rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
      Nat.shiftRight_eq_div_pow]
  have hmul : (q * dn2.toUInt64).toNat = q.toNat * dn2.toNat := by
    refine Nat.mod_eq_of_lt ?_
    calc q.toNat * dn2.toNat ≤ (base + 1) * (base - 1) := Nat.mul_le_mul hq (by omega)
      _ < 2 ^ 64 := by simp only [base_eq]; omega
  have hshl : ((r <<< 32) + nu.toUInt64).toNat = base * r.toNat + nu.toNat := by
    have h1 : (r <<< 32).toNat = r.toNat * 4294967296 := by
      rw [UInt64.toNat_shiftLeft, show (32 : UInt64).toNat % 64 = 32 from rfl]
      simp only [base_eq] at hr; omega
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64,
      Nat.mod_eq_of_lt (by simp only [base_eq] at hr hnu ⊢; omega)]
    simp only [base_eq]
    omega
  simp only [bne_iff_ne, ne_eq, UInt64.lt_iff_toNat_lt, hmul, hshl,
    Bool.or_eq_true, decide_eq_true_eq]
  have hz : (¬ (q >>> 32 = 0)) = (base ≤ q.toNat) := by
    rw [eq_iff_iff]
    constructor
    · intro h
      have : (q >>> 32).toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by rw [h0]; rfl))
      simp only [base_eq]; omega
    · intro h h0
      have : (q >>> 32).toNat = 0 := by rw [h0]; rfl
      simp only [base_eq] at h; omega
  rw [hz]

private theorem shr32_lt (x : DoubleDigit) : ((x >>> 32 == 0) = true) = (x.toNat < base) := by
  have hshr : (x >>> 32).toNat = x.toNat / 4294967296 := by
    rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
      Nat.shiftRight_eq_div_pow]
  simp [eq_iff_iff]
  constructor
  · intro h
    have : (x >>> 32).toNat = 0 := by rw [h]; rfl
    omega
  · intro h
    refine UInt64.toNat_inj.mp ?_
    grind

private theorem toNat_pred {q : DoubleDigit} (h : 0 < q.toNat) :
    (q - 1).toNat = q.toNat - 1 := by
  have := q.toNat_lt_size
  simp [UInt64.toNat_sub, UInt64.size] at *; omega

private theorem toNat_add_digit (r : DoubleDigit) (d : Digit) (hr : r.toNat < base) :
    (r + d.toUInt64).toNat = r.toNat + d.toNat := by
  have hd : d.toNat < base := d.toNat_lt_size
  simp only [base_eq] at hr hd
  rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
  exact Nat.mod_eq_of_lt (by omega)

/--
Step D3's postcondition: the trial digit it returns fits in a single digit and
is either exact or one too big, which is what makes the single add-back of step
D6 enough. Every decrement it performs is justified, so it never undershoots.
-/
theorem recheck_spec (dn1 dn2 nu : Digit) (k vrest ulow u2 V U : Nat)
    (hV : V = (dn1.toNat * base + dn2.toNat) * base ^ k + vrest)
    (hU : U = u2 * base ^ (k+1) + nu.toNat * base ^ k + ulow)
    (hnorm : base ≤ 2 * dn1.toNat)
    (hvrest : vrest < base ^ k) (hulow : ulow < base ^ k)
    (hu2 : u2 ≤ dn1.toNat * base + (base - 1))
    (hUV : U < V * base) :
    ∀ q r : DoubleDigit,
      u2 = q.toNat * dn1.toNat + r.toNat → r.toNat < base → U / V ≤ q.toNat →
      (recheck dn1 dn2 nu q r).1.toNat < base ∧
      U / V ≤ (recheck dn1 dn2 nu q r).1.toNat ∧
      (recheck dn1 dn2 nu q r).1.toNat ≤ U / V + 1 := by
  have hvtop1 : 1 ≤ dn1.toNat := by simp only [base_eq] at hnorm; omega
  have hd2 : dn2.toNat < base := dn2.toNat_lt_size
  have hVpos : 0 < V := by
    have h1 : 1 * base ^ k ≤ (dn1.toNat * base + dn2.toNat) * base ^ k :=
      Nat.mul_le_mul_right _ (by simp only [base_eq] at hvtop1 ⊢; omega)
    omega
  have hqlt : U / V < base := Nat.div_lt_of_lt_mul hUV
  -- a firing test always means the estimate is genuinely too big
  have fires : ∀ q r : DoubleDigit, u2 = q.toNat * dn1.toNat + r.toNat → r.toNat < base →
      (q >>> 32 != 0 || q * dn2.toUInt64 > ((r <<< 32) + nu.toUInt64)) = true →
      U / V < q.toNat := by
    intro q r hinv hr hfire
    have hq := q_le_of_inv hinv hu2 hnorm
    rw [recheck_test_iff dn2 nu q r hq hr] at hfire
    rcases hfire with h | h
    · omega
    · exact KnuthD.div_lt_of_test hV hVpos hU hulow hinv h
  -- exit with the test failing: `le_succ_div_of_not_test` applies directly
  have exitFail : ∀ q r : DoubleDigit, u2 = q.toNat * dn1.toNat + r.toNat → r.toNat < base →
      U / V ≤ q.toNat →
      ¬ ((q >>> 32 != 0 || q * dn2.toUInt64 > ((r <<< 32) + nu.toUInt64)) = true) →
      q.toNat < base ∧ U / V ≤ q.toNat ∧ q.toNat ≤ U / V + 1 := by
    intro q r hinv hr hle hfail
    have hq := q_le_of_inv hinv hu2 hnorm
    have harith : ¬ (base ≤ q.toNat ∨ base * r.toNat + nu.toNat < q.toNat * dn2.toNat) := by
      rw [← recheck_test_iff dn2 nu q r hq hr]; exact hfail
    have hf1 : q.toNat < base := by omega
    have hf2 : q.toNat * dn2.toNat ≤ base * r.toNat + nu.toNat := by omega
    exact ⟨hf1, hle, KnuthD.le_succ_div_of_not_test hV hVpos hU hinv hvrest hvtop1 hf1 hf2⟩
  -- exit with `r_hat` past the base: the test would fail there anyway
  have exitBig : ∀ q r : DoubleDigit, u2 = q.toNat * dn1.toNat + r.toNat → r.toNat < base →
      U / V < q.toNat → base ≤ (r + dn1.toUInt64).toNat →
      (q - 1).toNat < base ∧ U / V ≤ (q - 1).toNat ∧ (q - 1).toNat ≤ U / V + 1 := by
    intro q r hinv hr hdec hrbig
    have hqpos : 0 < q.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hdec
    have hqn : (q - 1).toNat = q.toNat - 1 := toNat_pred hqpos
    have hrn : (r + dn1.toUInt64).toNat = r.toNat + dn1.toNat := toNat_add_digit r dn1 hr
    have hinv' : u2 = (q - 1).toNat * dn1.toNat + (r + dn1.toUInt64).toNat := by
      obtain ⟨m, hm⟩ : ∃ m, q.toNat = m + 1 :=
        ⟨q.toNat - 1, (Nat.succ_pred_eq_of_pos hqpos).symm⟩
      rw [hm] at hinv
      grind
    have hqsmall : (q - 1).toNat < base := by
      refine Nat.lt_of_mul_lt_mul_right (a := dn1.toNat) ?_
      simp only [base_eq] at hu2 hrbig hinv' ⊢; omega
    refine ⟨hqsmall, by rw [hqn]; exact Nat.le_pred_of_lt hdec, ?_⟩
    refine KnuthD.le_succ_div_of_not_test hV hVpos hU hinv' hvrest hvtop1 hqsmall ?_
    calc (q - 1).toNat * dn2.toNat ≤ (base - 1) * (base - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ base * (r + dn1.toUInt64).toNat := by
          have h1 : base * base ≤ base * (r + dn1.toUInt64).toNat := Nat.mul_le_mul_left _ hrbig
          simp only [base_eq] at h1 ⊢; omega
      _ ≤ base * (r + dn1.toUInt64).toNat + nu.toNat := Nat.le_add_right _ _
  -- the loop itself, by induction on a bound for the trial digit
  have main : ∀ (n : Nat) (q r : DoubleDigit), q.toNat ≤ n →
      u2 = q.toNat * dn1.toNat + r.toNat → r.toNat < base → U / V ≤ q.toNat →
      (recheck dn1 dn2 nu q r).1.toNat < base ∧
      U / V ≤ (recheck dn1 dn2 nu q r).1.toNat ∧
      (recheck dn1 dn2 nu q r).1.toNat ≤ U / V + 1 := by
    intro n
    induction n with
    | zero =>
      intro q r hqn hinv hr hle
      by_cases hfire : (q >>> 32 != 0 || q * dn2.toUInt64 > ((r <<< 32) + nu.toUInt64)) = true
      · grind
      · rw [recheck.eq_def]
        simp [Bool.eq_false_iff.mpr hfire]
        exact exitFail q r hinv hr hle hfire
    | succ n ih =>
      intro q r hqn hinv hr hle
      by_cases hfire : (q >>> 32 != 0 || q * dn2.toUInt64 > ((r <<< 32) + nu.toUInt64)) = true
      · have hdec := fires q r hinv hr hfire
        have hqpos : 0 < q.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hdec
        have hqp : (q - 1).toNat = q.toNat - 1 := toNat_pred hqpos
        have hrn : (r + dn1.toUInt64).toNat = r.toNat + dn1.toNat := toNat_add_digit r dn1 hr
        by_cases hr2 : ((r + dn1.toUInt64) >>> 32 == 0) = true
        · have hrlt : (r + dn1.toUInt64).toNat < base := by rw [← shr32_lt]; exact hr2
          rw [recheck.eq_def]
          simp only [hfire, hr2]
          refine ih (q - 1) (r + dn1.toUInt64)
            (by rw [hqp]
                exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.sub_lt hqpos Nat.one_pos) hqn))
            ?_ hrlt (by rw [hqp]; exact Nat.le_pred_of_lt hdec)
          obtain ⟨m, hm⟩ : ∃ m, q.toNat = m + 1 :=
            ⟨q.toNat - 1, (Nat.succ_pred_eq_of_pos hqpos).symm⟩
          rw [hrn]
          rw [hm] at hinv
          grind
        · have hrbig : base ≤ (r + dn1.toUInt64).toNat := by
            rcases Nat.lt_or_ge (r + dn1.toUInt64).toNat base with h | h
            · exact absurd (shr32_lt (r + dn1.toUInt64) ▸ h) hr2
            · exact h
          simp [recheck.eq_def, hfire, Bool.eq_false_iff.mpr hr2]
          exact exitBig q r hinv hr hdec hrbig
      · rw [recheck.eq_def]
        simp [Bool.eq_false_iff.mpr hfire]
        exact exitFail q r hinv hr hle hfire
  intro q r h1 h2 h3
  exact main q.toNat q r (Nat.le_refl _) h1 h2 h3

/-! ## Slices -/

theorem getD_extract (a : Array Digit) (j k i : Nat) (h : i < k - j) (hk : k ≤ a.size) :
    (a.extract j k).getD i 0 = a.getD (j+i) 0 := by
  have h2 : j + i < a.size := by omega
  simp [h2, Nat.min_eq_left hk, h]

theorem denote_extract_zero (a : Array Digit) (j : Nat) : denote (a.extract j j) = 0 := by
  rw [denote]
  have : (a.extract j j).size = 0 := by grind
  rw [this]; rfl

/-- Reading a slice out of the middle: `a`'s low digits plus the slice, shifted. -/
theorem denoteN_extract (a : Array Digit) {j : Nat} :
    ∀ k, j ≤ k → k ≤ a.size →
      denoteN a k = denoteN a j + denote (a.extract j k) * base ^ j := by
  intro k
  induction k with
  | zero =>
    intro hjk _
    have : j = 0 := by omega
    subst this
    rw [denote_extract_zero]; simp [denoteN]
  | succ k ih =>
    intro hjk hk
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · subst h
      rw [denote_extract_zero]
      omega
    · have hjk' : j ≤ k := by omega
      have hsz : (a.extract j (k+1)).size = k + 1 - j := by grind
      have hpush : denote (a.extract j (k+1))
          = denote (a.extract j k) + (a.getD k 0).toNat * base ^ (k - j) := by
        have hsz' : (a.extract j k).size = k - j := by grind
        have hagree : ∀ i, i < k - j →
            (a.extract j (k+1)).getD i 0 = (a.extract j k).getD i 0 := by
          intro i hi
          rw [getD_extract a j (k+1) i (by omega) (by omega),
            getD_extract a j k i (by omega) (by omega)]
        have hlast : (a.extract j (k+1)).getD (k - j) 0 = a.getD k 0 := by
          rw [getD_extract a j (k+1) (k-j) (by omega) (by omega)]
          congr 1; omega
        rw [denote, hsz, show k + 1 - j = (k - j) + 1 by omega, denoteN,
          denoteN_congr hagree, hlast, denote, hsz']
      rw [denoteN, hpush, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add,
        show k - j + j = k by omega]
      omega

/-! ## Bulk digit copies -/

theorem size_copyInto (dst src : Array Digit) (j len : Nat) :
    (copyInto dst src j len).size = dst.size := by
  induction len with
  | zero => rfl
  | succ len ih => rw [copyInto_succ, size_set!, ih]

theorem getD_copyInto_of_lt (dst src : Array Digit) (j len i : Nat) (h : i < j) :
    (copyInto dst src j len).getD i 0 = dst.getD i 0 := by
  induction len with
  | zero => rfl
  | succ len ih => rw [copyInto_succ, getD_set!_ne _ _ _ _ (by omega), ih]

theorem getD_copyInto_of_ge (dst src : Array Digit) (j len i : Nat) (h : j + len ≤ i) :
    (copyInto dst src j len).getD i 0 = dst.getD i 0 := by
  induction len with
  | zero => rfl
  | succ len ih => rw [copyInto_succ, getD_set!_ne _ _ _ _ (by omega), ih (by omega)]

theorem denoteN_copyInto (dst src : Array Digit) (j : Nat) :
    ∀ len, j + len ≤ dst.size →
      denoteN (copyInto dst src j len) (j + len) = denoteN dst j + denoteN src len * base ^ j := by
  intro len
  induction len with
  | zero => intro _; simp [copyInto, denoteN]
  | succ len ih =>
    intro h
    have hsz : (copyInto dst src j len).size = dst.size := size_copyInto ..
    rw [show j + (len+1) = (j + len) + 1 by omega, copyInto_succ,
      denoteN_set!_succ _ _ _ (by rw [hsz]; omega), denoteN,
      Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, show len + j = j + len by omega]
    omega

theorem getD_copyInto_mid (dst src : Array Digit) (j : Nat) :
    ∀ len i, j ≤ i → i < j + len → j + len ≤ dst.size →
      (copyInto dst src j len).getD i 0 = src.getD (i - j) 0 := by
  intro len
  induction len with
  | zero => omega
  | succ len ih =>
    intro i h1 h2 h3
    rcases Nat.lt_or_ge i (j + len) with h | h
    · rw [copyInto_succ, getD_set!_ne _ _ _ _ (by omega)]
      exact ih i h1 h (by omega)
    · have hi : i = j + len := by omega
      subst hi
      rw [copyInto_succ, getD_set!_eq _ _ _ (by rw [size_copyInto]; omega)]
      simp

/-- After a copy, the window at `j` reads back exactly the digits that were written. -/
theorem denote_extract_copyInto (dst src : Array Digit) (j len : Nat)
    (hsz : j + len ≤ dst.size) :
    denote ((copyInto dst src j len).extract j (j + len)) = denoteN src len := by
  have hcsz : (copyInto dst src j len).size = dst.size := size_copyInto ..
  have hesz : ((copyInto dst src j len).extract j (j + len)).size = len := by grind
  have hagree : ∀ i, i < len →
      ((copyInto dst src j len).extract j (j + len)).getD i 0 = src.getD i 0 := by
    intro i hi
    rw [getD_extract _ j (j + len) i (by omega) (by rw [hcsz]; omega),
      getD_copyInto_mid dst src j len (j + i) (by omega) (by omega) hsz]
    congr 1
    omega
  rw [denote, hesz, denoteN_congr hagree]

/-! ## Two-digit decomposition -/

/-- The top two digits of an `n+2`-digit array, split off. -/
theorem denoteN_split_two (a : Array Digit) (k : Nat) :
    denoteN a (k+2)
      = ((a.getD (k+1) 0).toNat * base + (a.getD k 0).toNat) * base ^ k + denoteN a k := by
  have hp : base ^ (k+1) = base ^ k * base := Nat.pow_succ base k
  rw [denoteN, denoteN, hp]
  grind

/-- The same split for an `n+3`-digit window, in the shape Algorithm D uses. -/
theorem denoteN_split_window (a : Array Digit) (k : Nat) :
    denoteN a (k+3)
      = ((a.getD (k+2) 0).toNat * base + (a.getD (k+1) 0).toNat) * base ^ (k+1)
        + (a.getD k 0).toNat * base ^ k + denoteN a k := by
  have hp : base ^ (k+2) = base ^ (k+1) * base := Nat.pow_succ base (k+1)
  rw [denoteN, denoteN, denoteN, hp]
  grind

/-! ## Truncation -/

private theorem denoteN_add_high (a : Array Digit) (m : Nat) :
    ∀ n, m ≤ n → ∃ K, denoteN a n = denoteN a m + K * base ^ m := by
  intro n
  induction n with
  | zero => intro h; exact ⟨0, by have : m = 0 := by omega
                                  subst this; simp⟩
  | succ n ih =>
    intro h
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact ⟨0, by rw [← h']; simp⟩
    · obtain ⟨K, hK⟩ := ih (by omega)
      refine ⟨K + (a.getD n 0).toNat * base ^ (n - m), ?_⟩
      rw [denoteN, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add,
        show n - m + m = n by omega]
      omega

/-- Reading only the first `m` digits is truncation to `base ^ m`. -/
theorem denoteN_mod (a : Array Digit) (m : Nat) : denoteN a m = denote a % base ^ m := by
  rcases Nat.lt_or_ge m a.size with h | h
  · obtain ⟨K, hK⟩ := denoteN_add_high a m a.size (by omega)
    rw [denote, hK, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (denoteN_lt a m)]
  · rw [denoteN_of_ge a h, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le (denoteN_lt a a.size)
      (Nat.pow_le_pow_right (by simp [base_eq]) h)

theorem denote_singleton (x : Digit) : denote #[x] = x.toNat := by
  simp [denote, denoteN]

theorem size_sub (a b : Array Digit) : (sub a b).1.size = max a.size b.size :=
  (subLoop_spec a b (max a.size b.size)).1

/-! ## Correctness of `div_n` -/

/--
The trial digit `div_n` computes for the window at `j` is exact or one too high.
This is `recheck_spec` with the window's digits read off the array.
-/
theorem divNTrial_spec (denom u : Array Digit) (j k : Nat)
    (hk : denom.size = k + 2)
    (hnorm : base ≤ 2 * (denom.getD (k+1) 0).toNat)
    (hsz : j + k + 3 ≤ u.size)
    (hW : denote (u.extract j (j+k+3)) < denote denom * base) :
    denote (u.extract j (j+k+3)) / denote denom ≤ (divNTrial denom u (norm_top_ne_zero hk hnorm) j).toNat ∧
    (divNTrial denom u (norm_top_ne_zero hk hnorm) j).toNat ≤ denote (u.extract j (j+k+3)) / denote denom + 1 := by
  have hvtop1 : 1 ≤ (denom.getD (k+1) 0).toNat := by grind
  have hpk1 : 0 < base ^ (k+1) := Nat.pow_pos (by simp [base_eq])
  -- the divisor, split at its top two digits
  have hV : denote denom
      = ((denom.getD (k+1) 0).toNat * base + (denom.getD k 0).toNat) * base ^ k + denoteN denom k := by
    rw [denote, hk]; exact denoteN_split_two denom k
  have hvrest : denoteN denom k < base ^ k := denoteN_lt denom k
  -- the window, split in the shape step D3 reads it
  have hWsz : (u.extract j (j+k+3)).size = k + 3 := by grind
  have hwin : ∀ i, i < k + 3 → (u.extract j (j+k+3)).getD i 0 = u.getD (j+i) 0 :=
    fun i hi => getD_extract u j (j+k+3) i (by omega) (by omega)
  have hU : denote (u.extract j (j+k+3))
      = ((u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat) * base ^ (k+1)
        + (u.getD (j+k) 0).toNat * base ^ k + denoteN (u.extract j (j+k+3)) k := by
    rw [denote, hWsz, denoteN_split_window]
    rw [hwin (k+2) (by omega), hwin (k+1) (by omega), hwin k (by omega)]
    rfl
  have hulow : denoteN (u.extract j (j+k+3)) k < base ^ k := denoteN_lt _ k
  -- the two-digit window that the trial digit is computed from
  have htemp : ((((u.getD (j+k+2) 0).toUInt64 <<< 32) ||| (u.getD (j+k+1) 0).toUInt64)).toNat
      = (u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat := toNat_window _ _
  have hq0 : ((((u.getD (j+k+2) 0).toUInt64 <<< 32) ||| (u.getD (j+k+1) 0).toUInt64)
        / (denom.getD (k+1) 0).toUInt64).toNat
      = ((u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat)
          / (denom.getD (k+1) 0).toNat := by
    rw [UInt64.toNat_div, htemp, UInt32.toNat_toUInt64]
  have hr0 : ((((u.getD (j+k+2) 0).toUInt64 <<< 32) ||| (u.getD (j+k+1) 0).toUInt64)
        % (denom.getD (k+1) 0).toUInt64).toNat
      = ((u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat)
          % (denom.getD (k+1) 0).toNat := by
    rw [UInt64.toNat_mod, htemp, UInt32.toNat_toUInt64]
  -- the loop invariant of step D3 holds on entry
  have hinv0 : (u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat
      = ((((u.getD (j+k+2) 0).toUInt64 <<< 32) ||| (u.getD (j+k+1) 0).toUInt64)
          / (denom.getD (k+1) 0).toUInt64).toNat * (denom.getD (k+1) 0).toNat
        + ((((u.getD (j+k+2) 0).toUInt64 <<< 32) ||| (u.getD (j+k+1) 0).toUInt64)
          % (denom.getD (k+1) 0).toUInt64).toNat := by
    rw [hq0, hr0]; exact (Nat.div_add_mod' _ _).symm
  have hrlt : ((((u.getD (j+k+2) 0).toUInt64 <<< 32) ||| (u.getD (j+k+1) 0).toUInt64)
        % (denom.getD (k+1) 0).toUInt64).toNat < base := by
    rw [hr0]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega))
      (Nat.le_of_lt (denom.getD (k+1) 0).toNat_lt_size)
  -- the divisor's leading digit bounds the two-digit window
  have hVlt : denote denom < ((denom.getD (k+1) 0).toNat + 1) * base ^ (k+1) := by
    have hd2 : (denom.getD k 0).toNat < base := (denom.getD k 0).toNat_lt_size
    have hstep : (denom.getD k 0).toNat * base ^ k + denoteN denom k < base ^ (k+1) := by
      have h1 : (denom.getD k 0).toNat * base ^ k ≤ (base - 1) * base ^ k :=
        Nat.mul_le_mul_right _ (by simp only [base_eq] at hd2 ⊢; omega)
      have h2 : (base - 1) * base ^ k + base ^ k = base ^ (k+1) := by
        simp [ base]; omega
      omega
    have h3 : ((denom.getD (k+1) 0).toNat + 1) * base ^ (k+1)
        = (denom.getD (k+1) 0).toNat * base * base ^ k + base ^ (k+1) := by
      grind
    rw [hV, Nat.add_mul]
    omega
  have hu2bound : (u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat
      ≤ (denom.getD (k+1) 0).toNat * base + (base - 1) := by
    have hge : ((u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat) * base ^ (k+1)
        ≤ denote (u.extract j (j+k+3)) := by rw [hU]; omega
    have hlt : denote (u.extract j (j+k+3))
        < (((denom.getD (k+1) 0).toNat + 1) * base) * base ^ (k+1) := by
      calc denote (u.extract j (j+k+3)) < denote denom * base := hW
        _ < (((denom.getD (k+1) 0).toNat + 1) * base ^ (k+1)) * base :=
            (Nat.mul_lt_mul_right (by simp [base_eq])).mpr hVlt
        _ = (((denom.getD (k+1) 0).toNat + 1) * base) * base ^ (k+1) := by grind
    have := Nat.lt_of_mul_lt_mul_right (a := base ^ (k+1)) (Nat.lt_of_le_of_lt hge hlt)
    simp only [base_eq] at this ⊢; omega
  -- Theorem A: the initial estimate is not too small
  have hle0 : denote (u.extract j (j+k+3)) / denote denom
      ≤ ((u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat)
          / (denom.getD (k+1) 0).toNat := by
    have hVd : denote denom / base ^ (k+1) = (denom.getD (k+1) 0).toNat := by
      rw [hV]
      have h1 : ((denom.getD (k+1) 0).toNat * base + (denom.getD k 0).toNat) * base ^ k
          + denoteN denom k
          = (denom.getD (k+1) 0).toNat * base ^ (k+1)
            + ((denom.getD k 0).toNat * base ^ k + denoteN denom k) := by
        grind
      have h2 : (denom.getD k 0).toNat * base ^ k + denoteN denom k < base ^ (k+1) := by
        have hd2 : (denom.getD k 0).toNat < base := (denom.getD k 0).toNat_lt_size
        have ha : (denom.getD k 0).toNat * base ^ k ≤ (base - 1) * base ^ k :=
          Nat.mul_le_mul_right _ (by simp only [base_eq] at hd2 ⊢; omega)
        have hb : (base - 1) * base ^ k + base ^ k = base ^ (k+1) := by
          simp [ base]; omega
        omega
      rw [h1, Nat.mul_comm, Nat.mul_add_div hpk1, Nat.div_eq_of_lt h2, Nat.add_zero]
    have hUd : denote (u.extract j (j+k+3)) / base ^ (k+1)
        = (u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat := by
      rw [hU]
      have h2 : (u.getD (j+k) 0).toNat * base ^ k + denoteN (u.extract j (j+k+3)) k
          < base ^ (k+1) := by
        have hd3 : (u.getD (j+k) 0).toNat < base := (u.getD (j+k) 0).toNat_lt_size
        have ha : (u.getD (j+k) 0).toNat * base ^ k ≤ (base - 1) * base ^ k :=
          Nat.mul_le_mul_right _ (by simp only [base_eq] at hd3 ⊢; omega)
        have hb : (base - 1) * base ^ k + base ^ k = base ^ (k+1) := by
          simp [Nat.pow_succ, base]; grind
        omega
      rw [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_div hpk1, Nat.div_eq_of_lt h2, Nat.add_zero]
    have := KnuthD.le_qhat (u := denote (u.extract j (j+k+3))) (v := denote denom)
      (P := base ^ (k+1)) hpk1 (by rw [hVd]; omega)
    rw [hVd, hUd] at this
    exact this
  obtain ⟨hqlt, hq1, hq2⟩ := recheck_spec (denom.getD (k+1) 0) (denom.getD k 0) (u.getD (j+k) 0) k
    (denoteN denom k) (denoteN (u.extract j (j+k+3)) k)
    ((u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat)
    (denote denom) (denote (u.extract j (j+k+3)))
    hV hU hnorm hvrest hulow hu2bound hW _ _ hinv0 hrlt (by rw [hq0]; exact hle0)
  have hdt : divNTrial denom u (norm_top_ne_zero hk hnorm) j
      = lo (recheck (denom.getD (k+1) 0) (denom.getD k 0) (u.getD (j+k) 0)
          ((((u.getD (j+k+2) 0).toUInt64 <<< 32) ||| (u.getD (j+k+1) 0).toUInt64)
            / (denom.getD (k+1) 0).toUInt64)
          ((((u.getD (j+k+2) 0).toUInt64 <<< 32) ||| (u.getD (j+k+1) 0).toUInt64)
            % (denom.getD (k+1) 0).toUInt64)).1 := by
    simp only [divNTrial, hk]
    rfl
  rw [hdt, lo_of_lt _ hqlt]
  exact ⟨hq1, hq2⟩



private theorem toNat_pred32 {q : Digit} (h : 0 < q.toNat) : (q - 1).toNat = q.toNat - 1 := by
  have := q.toNat_lt_size
  simp [UInt32.toNat_sub, UInt32.size] at *; omega

private theorem sub_eq_subLoop (a b : Array Digit) (len : Nat)
    (ha : a.size = len) (hb : b.size = len) : sub a b = subLoop a b len := by
  rw [sub_eq, ha, hb, Nat.max_self]

/--
Subtracting in place is subtracting into a fresh buffer and copying the result
back, which is what lets `div_n` pass `&numer[j]` as both an input and the
output of `mpn_sub`.
-/
theorem subInPlace_eq (u b : Array Digit) (off len : Nat) (hfits : off + len ≤ u.size) :
    subInPlace u b off len
      = (copyInto u (subLoop (u.extract off (off+len)) b len).1 off len,
         (subLoop (u.extract off (off+len)) b len).2) := by
  obtain ⟨hsz, hk, hdig, hout⟩ :=
    subInPlace_spec u b (u.extract off (off+len)) off len hfits
      (fun i hi => getD_extract u off (off+len) i (by omega) (by omega))
  refine Prod.ext ?_ hk
  refine array_ext_getD (by rw [hsz, size_copyInto]) (fun i => ?_)
  rcases Nat.lt_or_ge i off with h | h
  · rw [hout i (by omega), getD_copyInto_of_lt _ _ _ _ _ h]
  rcases Nat.lt_or_ge i (off + len) with h2 | h2
  · obtain ⟨t, ht⟩ : ∃ t, i = off + t := ⟨i - off, by omega⟩
    subst ht
    rw [hdig t (by omega), getD_copyInto_mid _ _ _ _ _ (by omega) (by omega) (by omega),
      Nat.add_sub_cancel_left]
  · rw [hout i (by omega), getD_copyInto_of_ge _ _ _ _ _ h2]

/--
One step of `div_n`: it writes the true quotient digit and leaves the window
holding the partial remainder, which is below the divisor.
-/
theorem divNStep_spec (denom u quot : Array Digit) (j k m : Nat)
    (hk : denom.size = k + 2)
    (hnorm : base ≤ 2 * (denom.getD (k+1) 0).toNat)
    (husz : u.size = m + denom.size)
    (hqsz : quot.size = m)
    (hj : j < m)
    (hqj : quot.getD j 0 = 0)
    (hhigh : ∀ i, j + 1 + denom.size ≤ i → u.getD i 0 = 0)
    (hbound : denote u < denote denom * base ^ (j+1)) :
    (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) j).1.size = u.size ∧
    (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) j).2.size = m ∧
    (∀ i, j + denom.size ≤ i → (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) j).1.getD i 0 = 0) ∧
    (∀ i, i ≠ j → (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) j).2.getD i 0 = quot.getD i 0) ∧
    denote (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) j).1 < denote denom * base ^ j ∧
    denote (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) j).2 * denote denom
        + denote (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) j).1
      = denote quot * denote denom + denote u := by
  have hjs : j + denom.size + 1 = j + k + 3 := by omega
  have hsz3 : j + k + 3 ≤ u.size := by omega
  have hVlt : denote denom < base ^ (k+2) := by
    have h := denoteN_lt denom denom.size
    rw [← denote, hk] at h; exact h
  have hVpos : 0 < denote denom := by
    grind
  -- the window, and its bound
  have hwin_eq : denote u = denoteN u j + denote (u.extract j (j+k+3)) * base ^ j := by
    rw [denote_of_high_zero u (n := j+k+3) (by omega) (fun i hi => hhigh i (by omega))]
    exact denoteN_extract u (j+k+3) (by omega) (by omega)
  have hW : denote (u.extract j (j+k+3)) < denote denom * base := by
    have h1 : denote (u.extract j (j+k+3)) * base ^ j ≤ denote u := by omega
    have h2 : denote denom * base ^ (j+1) = denote denom * base * base ^ j := by
      grind
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt h1 (h2 ▸ hbound))
  obtain ⟨hq1, hq2⟩ := divNTrial_spec denom u j k hk hnorm hsz3 hW
  -- name the pieces of the step
  obtain ⟨q, hq⟩ : ∃ x, x = divNTrial denom u (norm_top_ne_zero hk hnorm) j := ⟨_, rfl⟩
  obtain ⟨ms, hms⟩ : ∃ x, x = mul #[q] denom := ⟨_, rfl⟩
  obtain ⟨dw, hdw⟩ : ∃ x, x = sub (u.extract j (j + denom.size + 1)) ms := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ x, x = copyInto u dw.1 j (denom.size + 1) := ⟨_, rfl⟩
  rw [← hq] at hq1 hq2
  -- the in-place subtraction agrees with subtracting into a fresh buffer
  have hip : subInPlace u ms j (denom.size + 1) = (u1, dw.2) := by
    have hdwl : dw = subLoop (u.extract j (j + (denom.size + 1))) ms (denom.size + 1) := by
      rw [hdw, show j + denom.size + 1 = j + (denom.size + 1) from by omega]
      exact sub_eq_subLoop _ _ _ (by simp; omega) (by rw [hms, size_mul]; exact Nat.add_comm _ _)
    rw [subInPlace_eq u ms j (denom.size + 1) (by omega), hu1, hdwl]
  have hstep : divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) j =
      if dw.2 != 0 then
        (copyInto u1 (add denom (u1.extract j (j + denom.size + 1))) j (denom.size + 1),
         quot.set! j (q - 1))
      else (u1, quot.set! j q) := by
    simp only [divNStep, ← hq, ← hms, hip]
  -- the subtraction
  have hmssz : ms.size = 1 + denom.size := by rw [hms]; exact size_mul ..
  have hmsval : denote ms = q.toNat * denote denom := by
    rw [hms, denote_mul, denote_singleton]
  have hmax : max (u.extract j (j + denom.size + 1)).size ms.size = denom.size + 1 := by
    grind
  have hdwsz : dw.1.size = denom.size + 1 := by rw [hdw, size_sub, hmax]
  have hdwval : denote dw.1 + denote ms
      = denote (u.extract j (j+k+3)) + dw.2.toNat * base ^ (denom.size + 1) := by
    have h := denote_sub (u.extract j (j + denom.size + 1)) ms
    rw [hmax] at h
    rw [hdw, hjs] at *
    exact h
  have hdwlt : denote dw.1 < base ^ (denom.size + 1) := by
    rw [denote, hdwsz]; exact denoteN_lt _ _
  have hb1 : dw.2.toNat ≤ 1 := by
    rw [hdw]; exact (subLoop_spec (u.extract j (j + denom.size + 1)) ms _).2.1
  -- what the copy does to `u`
  have hu1sz : u1.size = u.size := by rw [hu1]; exact size_copyInto ..
  have hu1win : denote (u1.extract j (j + denom.size + 1)) = denote dw.1 := by
    rw [hu1, show j + denom.size + 1 = j + (denom.size + 1) from by omega,
      denote_extract_copyInto u dw.1 j (denom.size + 1) (by omega), denote, hdwsz]
  have hu1low : ∀ i, i < j → u1.getD i 0 = u.getD i 0 :=
    fun i hi => by rw [hu1]; exact getD_copyInto_of_lt u dw.1 j (denom.size+1) i hi
  have hu1high : ∀ i, j + denom.size + 1 ≤ i → u1.getD i 0 = u.getD i 0 :=
    fun i hi => by rw [hu1]; exact getD_copyInto_of_ge u dw.1 j (denom.size+1) i (by omega)
  -- everything downstream of the step depends only on the final window value
  have final : ∀ (u' : Array Digit) (qd : Digit),
      u'.size = u.size →
      (∀ i, i < j → u'.getD i 0 = u.getD i 0) →
      (∀ i, j + denom.size + 1 ≤ i → u'.getD i 0 = u.getD i 0) →
      denote (u'.extract j (j + denom.size + 1))
        = denote (u.extract j (j+k+3)) % denote denom →
      qd.toNat = denote (u.extract j (j+k+3)) / denote denom →
      u'.size = u.size ∧ (quot.set! j qd).size = m ∧
      (∀ i, j + denom.size ≤ i → u'.getD i 0 = 0) ∧
      (∀ i, i ≠ j → (quot.set! j qd).getD i 0 = quot.getD i 0) ∧
      denote u' < denote denom * base ^ j ∧
      denote (quot.set! j qd) * denote denom + denote u'
        = denote quot * denote denom + denote u := by
    intro u' qd hsz' hlow' hhigh' hwin' hqd
    have hmodlt : denote (u.extract j (j+k+3)) % denote denom < denote denom :=
      Nat.mod_lt _ hVpos
    have hu'sz0 : j + denom.size + 1 ≤ u'.size := by rw [hsz']; omega
    have hextsz' : (u'.extract j (j + denom.size + 1)).size = denom.size + 1 := by
      grind
    -- the window's top digit has become zero
    have htop : u'.getD (j + denom.size) 0 = 0 := by
      have hsplit : denote (u'.extract j (j + denom.size + 1))
          = denoteN (u'.extract j (j + denom.size + 1)) (k+2)
            + ((u'.extract j (j + denom.size + 1)).getD (k+2) 0).toNat * base ^ (k+2) := by
        rw [denote, hextsz', show denom.size + 1 = (k+2) + 1 from by omega, denoteN]
      have hgetd : (u'.extract j (j + denom.size + 1)).getD (k+2) 0 = u'.getD (j + denom.size) 0 := by
        rw [getD_extract u' j (j + denom.size + 1) (k+2) (by omega) hu'sz0]
        congr 1; omega
      rw [hgetd] at hsplit
      rcases Nat.eq_zero_or_pos (u'.getD (j + denom.size) 0).toNat with h | h
      · exact UInt32.toNat_inj.mp (by rw [h]; rfl)
      · exfalso
        have hmul : base ^ (k+2) ≤ (u'.getD (j + denom.size) 0).toNat * base ^ (k+2) :=
          Nat.le_mul_of_pos_left _ h
        have hge : base ^ (k+2) ≤ denote (u'.extract j (j + denom.size + 1)) := by
          omega
        rw [hwin'] at hge
        omega
    have hzero : ∀ i, j + denom.size ≤ i → u'.getD i 0 = 0 := by
      grind
    have hden' : denote u' = denoteN u j + (denote (u.extract j (j+k+3)) % denote denom) * base ^ j := by
      have hu'sz : j + denom.size + 1 ≤ u'.size := by rw [hsz']; omega
      rw [denote_of_high_zero u' (n := j + denom.size + 1) hu'sz
          (fun i hi => hzero i (by omega)),
        denoteN_extract (j := j) u' (j + denom.size + 1) (by omega) hu'sz, hwin',
        denoteN_congr (c' := u) (fun i hi => hlow' i hi)]
    refine ⟨hsz', by simp [hqsz], hzero, ?_, ?_, ?_⟩
    · intro i hi; exact getD_set!_ne quot j i qd hi
    · have h1 : denoteN u j < base ^ j := denoteN_lt u j
      have h2 : (denote (u.extract j (j+k+3)) % denote denom) * base ^ j
          ≤ (denote denom - 1) * base ^ j := Nat.mul_le_mul_right _ (by omega)
      have h3 : (denote denom - 1) * base ^ j + base ^ j = denote denom * base ^ j := by
        obtain ⟨V', hV'⟩ : ∃ V', denote denom = V' + 1 := ⟨denote denom - 1, by omega⟩
        rw [hV', Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
      omega
    · rw [denote_set!_of_zero quot j qd (by omega) hqj, hqd, hden', hwin_eq]
      have hdm := Nat.div_add_mod' (denote (u.extract j (j+k+3))) (denote denom)
      grind
  rw [hstep]
  have hdm := Nat.div_add_mod' (denote (u.extract j (j+k+3))) (denote denom)
  by_cases hb : (dw.2 != 0) = true
  · -- step D6 fired: the estimate was one too high, so add the divisor back
    simp only [hb, ite_true]
    have hne : dw.2 ≠ 0 := by simpa using hb
    have hnz : dw.2.toNat ≠ 0 := fun h => hne (UInt32.toNat_inj.mp (by rw [h]; rfl))
    have hb1' : dw.2.toNat = 1 := by omega
    rw [hmsval, hb1', Nat.one_mul] at hdwval
    have hqeq : q.toNat = denote (u.extract j (j+k+3)) / denote denom + 1 := by
      have hnle : ¬ (q.toNat ≤ denote (u.extract j (j+k+3)) / denote denom) := by
        intro h
        have hle2 : q.toNat * denote denom ≤ denote (u.extract j (j+k+3)) :=
          Nat.le_trans (Nat.mul_le_mul_right _ h) (Nat.div_mul_le_self _ _)
        omega
      omega
    have hqm1 : (q - 1).toNat = q.toNat - 1 :=
      toNat_pred32 (by rw [hqeq]; exact Nat.succ_pos _)
    have hqV : q.toNat * denote denom
        = denote (u.extract j (j+k+3)) / denote denom * denote denom + denote denom := by
      grind
    have habv : denote (add denom (u1.extract j (j + denom.size + 1)))
        = denote (u.extract j (j+k+3)) % denote denom + base ^ (denom.size + 1) := by
      rw [denote_add, hu1win]
      omega
    have hsmall : denote (u.extract j (j+k+3)) % denote denom < base ^ (denom.size + 1) := by
      have : base ^ (k+2) ≤ base ^ (denom.size + 1) :=
        Nat.pow_le_pow_right (by simp [base_eq]) (by omega)
      omega
    refine final _ (q - 1) (by rw [size_copyInto, hu1sz]) ?_ ?_ ?_ (by rw [hqm1, hqeq, Nat.add_sub_cancel])
    · intro i hi
      rw [getD_copyInto_of_lt _ _ _ _ _ hi]; exact hu1low i hi
    · intro i hi
      rw [getD_copyInto_of_ge _ _ _ _ _ (by omega)]; exact hu1high i hi
    · rw [show j + denom.size + 1 = j + (denom.size + 1) from by omega,
        denote_extract_copyInto u1 _ j (denom.size + 1) (by rw [hu1sz, husz]; omega),
        denoteN_mod,
        show j + (denom.size + 1) = j + denom.size + 1 from by omega, habv,
        Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]
  · -- no borrow: the estimate was exact
    simp only [Bool.eq_false_iff.mpr hb, Bool.false_eq_true, ite_false]
    have heq0 : dw.2 = 0 := by simpa using hb
    have hb0 : dw.2.toNat = 0 := by rw [heq0]; rfl
    rw [hmsval, hb0, Nat.zero_mul, Nat.add_zero] at hdwval
    have hqeq : q.toNat = denote (u.extract j (j+k+3)) / denote denom := by
      have hle2 : q.toNat * denote denom ≤ denote (u.extract j (j+k+3)) := by omega
      have := (Nat.le_div_iff_mul_le hVpos).mpr hle2
      omega
    have hdw_eq : denote dw.1 = denote (u.extract j (j+k+3)) % denote denom := by
      grind
    exact final u1 q hu1sz hu1low hu1high (by rw [hu1win, hdw_eq]) hqeq

/--
The loop invariant of `div_n`: the quotient digits written so far times the
divisor, plus what is left in `u`, account for the numerator, and what is left
is always below the divisor scaled by the digits still to come.
-/
theorem divNLoop_spec (denom : Array Digit) (k m : Nat)
    (hk : denom.size = k + 2)
    (hnorm : base ≤ 2 * (denom.getD (k+1) 0).toNat) :
    ∀ (p : Nat) (u quot : Array Digit), p ≤ m →
      u.size = m + denom.size → quot.size = m →
      (∀ i, p + denom.size ≤ i → u.getD i 0 = 0) →
      (∀ i, i < p → quot.getD i 0 = 0) →
      denote u < denote denom * base ^ p →
      (divNLoop denom (norm_top_ne_zero hk hnorm) u quot p).1.size = m + denom.size ∧
      (divNLoop denom (norm_top_ne_zero hk hnorm) u quot p).2.size = m ∧
      denote (divNLoop denom (norm_top_ne_zero hk hnorm) u quot p).1 < denote denom ∧
      denote (divNLoop denom (norm_top_ne_zero hk hnorm) u quot p).2 * denote denom + denote (divNLoop denom (norm_top_ne_zero hk hnorm) u quot p).1
        = denote quot * denote denom + denote u := by
  intro p
  induction p with
  | zero =>
    intro u quot _ husz hqsz _ _ hbound
    refine ⟨husz, hqsz, ?_, rfl⟩
    simpa [divNLoop] using hbound
  | succ p ih =>
    intro u quot hp husz hqsz hhigh hqz hbound
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := divNStep_spec denom u quot p k m hk hnorm husz hqsz
      (by omega) (hqz p (by omega)) hhigh hbound
    rw [divNLoop_succ]
    obtain ⟨g1, g2, g3, g4⟩ := ih (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) p).1 (divNStep denom (norm_top_ne_zero hk hnorm) (u, quot) p).2
      (by omega) (by rw [h1, husz]) h2 h3
      (fun i hi => by rw [h4 i (by omega)]; exact hqz i (by omega)) h5
    exact ⟨g1, g2, g3, by rw [g4, h6]⟩

/-- `div_n` divides: quotient times divisor plus remainder is the numerator. -/
theorem divN_spec (numer denom : Array Digit) (k : Nat)
    (hk : denom.size = k + 2)
    (hnorm : base ≤ 2 * (denom.getD (k+1) 0).toNat)
    (hsz : denom.size ≤ numer.size)
    (hbound : denote numer < denote denom * base ^ (numer.size - denom.size)) :
    (divN numer denom (norm_top_ne_zero hk hnorm)).1.size = numer.size ∧
    (divN numer denom (norm_top_ne_zero hk hnorm)).2.size = numer.size - denom.size ∧
    denote (divN numer denom (norm_top_ne_zero hk hnorm)).1 < denote denom ∧
    denote (divN numer denom (norm_top_ne_zero hk hnorm)).2 * denote denom + denote (divN numer denom (norm_top_ne_zero hk hnorm)).1 = denote numer := by
  obtain ⟨g1, g2, g3, g4⟩ := divNLoop_spec denom k (numer.size - denom.size) hk hnorm
    (numer.size - denom.size) numer (Array.replicate (numer.size - denom.size) 0)
    (Nat.le_refl _) (by omega) (by simp) (fun i hi => getD_of_ge numer (by omega))
    (fun i _ => getD_replicate_zero _ _) hbound
  rw [divN_eq]
  refine ⟨by rw [g1]; omega, g2, g3, ?_⟩
  rw [g4, denote_replicate_zero, Nat.zero_mul, Nat.zero_add]

/-! ## Correctness of `mpn_div` -/

private theorem div_mod_of_eq {q V r N : Nat} (hV : 0 < V) (heq : q * V + r = N) (hr : r < V) :
    q = N / V ∧ r = N % V := by
  subst heq
  rw [Nat.mul_comm, Nat.mul_add_div hV, Nat.div_eq_of_lt hr, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  exact ⟨rfl, rfl⟩

/-- Same length, smaller leading digit: smaller number. -/
theorem denote_lt_of_top_lt (a b : Array Digit) (hs : a.size = b.size) (hpos : 0 < a.size)
    (h : (a.getD (a.size - 1) 0).toNat < (b.getD (b.size - 1) 0).toNat) : denote a < denote b := by
  obtain ⟨t, ht⟩ : ∃ t, a.size = t + 1 := ⟨a.size - 1, by omega⟩
  have hbt : b.size = t + 1 := by omega
  have hta : a.size - 1 = t := by omega
  have htb : b.size - 1 = t := by omega
  rw [hta, htb] at h
  have ha : denote a = denoteN a t + (a.getD t 0).toNat * base ^ t := by rw [denote, ht]; rfl
  have hb : denote b = denoteN b t + (b.getD t 0).toNat * base ^ t := by rw [denote, hbt]; rfl
  have h1 : denoteN a t < base ^ t := denoteN_lt a t
  have h3 : ((a.getD t 0).toNat + 1) * base ^ t ≤ (b.getD t 0).toNat * base ^ t :=
    Nat.mul_le_mul_right _ (by omega)
  grind

theorem denote_range_map (a : Array Digit) (n : Nat) (h : a.size = n) :
    denote ((Array.range n).map fun i => a.getD i 0) = denote a := by
  have hsz : ((Array.range n).map fun i => a.getD i 0).size = n := by simp
  rw [denote, hsz, denoteN_congr (c' := a) (fun i hi => by simp [hi]), denote, h]

theorem denote_copyInto_replicate (src : Array Digit) (n len : Nat) (h : len ≤ n) :
    denote (copyInto (Array.replicate n 0) src 0 len) = denoteN src len := by
  have hrsz : (Array.replicate n (0 : Digit)).size = n := by simp
  have hsz : (copyInto (Array.replicate n 0) src 0 len).size = n := by rw [size_copyInto, hrsz]
  have hhigh : ∀ i, len ≤ i → (copyInto (Array.replicate n 0) src 0 len).getD i 0 = 0 := by
    intro i hi
    rw [getD_copyInto_of_ge _ _ 0 len i (by omega)]
    exact getD_replicate_zero _ _
  rw [denote_of_high_zero _ (n := len) (by rw [hsz]; omega) hhigh]
  have hc := denoteN_copyInto (Array.replicate n 0) src 0 len (by rw [hrsz]; omega)
  simpa [denoteN] using hc

/--
`mpn_div` divides: what it returns are the quotient and remainder of the
operands. The preconditions are the ones every in-tree caller satisfies, since
`mpz` keeps its sizes normalized and `lean_nat_div` rejects a zero divisor.
-/
theorem div_spec (numer denom : Array Digit)
    (hden : 0 < denom.size) (hsz : denom.size ≤ numer.size)
    (htop : 0 < (denom.getD (denom.size - 1) 0).toNat) :
    denote (div numer denom hden hsz htop).1 = denote numer / denote denom ∧
    denote (div numer denom hden hsz htop).2 = denote numer % denote denom := by
  have hnum : 0 < numer.size := by omega
  have hVpos : 0 < denote denom := by
    obtain ⟨t, ht⟩ : ∃ t, denom.size = t + 1 := ⟨denom.size - 1, by omega⟩
    have hd : denote denom = denoteN denom t + (denom.getD t 0).toNat * base ^ t := by
      rw [denote, ht]; rfl
    have ht1 : denom.size - 1 = t := by omega
    rw [ht1] at htop
    have h1 : 1 * base ^ t ≤ (denom.getD t 0).toNat * base ^ t :=
      Nat.mul_le_mul_right _ (by omega)
    have hp : 0 < base ^ t := Nat.pow_pos (by simp [base_eq])
    omega
  rw [div]
  simp only [show ¬ (numer.size < denom.size) from by omega, dite_false]
  by_cases hB : (numer.size = 1 && denom.size = 1) = true
  · -- both single digit: the hardware divide
    simp only [hB, dite_true]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    have hN : denote numer = (numer.getD 0 0).toNat := by rw [denote, hB.1]; simp [denoteN]
    have hD : denote denom = (denom.getD 0 0).toNat := by rw [denote, hB.2]; simp [denoteN]
    simp only [CPP.div, CPP.mod]
    exact ⟨by rw [denote_singleton, UInt32.toNat_div, hN, hD],
      by rw [denote_singleton, UInt32.toNat_mod, hN, hD]⟩
  · simp only [Bool.eq_false_iff.mpr hB, Bool.false_eq_true, dite_false]
    by_cases hC : (numer.size = denom.size &&
        numer.getD (numer.size-1) 0 < denom.getD (denom.size-1) 0) = true
    · -- numerator already smaller: quotient zero
      simp only [hC, ite_true]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hC
      have hlt : denote numer < denote denom :=
        denote_lt_of_top_lt numer denom hC.1 hnum (by
          simpa [UInt32.lt_iff_toNat_lt] using hC.2)
      exact ⟨by rw [denote_replicate_zero, Nat.div_eq_of_lt hlt],
        by rw [denote_range_map numer denom.size hC.1, Nat.mod_eq_of_lt hlt]⟩
    · simp only [Bool.eq_false_iff.mpr hC, Bool.false_eq_true, ite_false]
      -- the general path: normalize, divide, unnormalize
      obtain ⟨dd, u, v, hduv⟩ : ∃ dd u v, divNormalize numer denom = (dd, u, v) := ⟨_, _, _, rfl⟩
      have hd32 : dd.val < digitBits := dd.isLt
      obtain ⟨husz, hvsz, huval, hvval, hvnorm⟩ :=
        divNormalize_spec numer denom hnum hden htop
      rw [hduv] at husz hvsz huval hvval hvnorm
      simp only [hduv]
      dsimp only at husz hvsz huval hvval hvnorm ⊢
      have hnzv : (v.getD (v.size - 1) 0).toUInt64 ≠ 0 := by
        rw [hvsz]; exact toUInt64_ne_zero (by omega)
      have h2d : 0 < 2 ^ dd.val := Nat.two_pow_pos _
      have hdle : (2:Nat) ^ dd.val ≤ 2147483648 := by
        simp only [digitBits_eq] at hd32
        calc (2:Nat) ^ dd.val ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) (by omega)
          _ = 2147483648 := rfl
      have hVpos' : 0 < denote v := by rw [hvval]; exact Nat.mul_pos hVpos h2d
      have hNlt : denote numer < base ^ numer.size := denoteN_lt numer numer.size
      -- the divisor's leading digit, and what it forces about `u`'s
      have hvsplit : denote v = denoteN v (denom.size - 1)
          + (v.getD (denom.size - 1) 0).toNat * base ^ (denom.size - 1) := by
        obtain ⟨t, ht⟩ : ∃ t, denom.size = t + 1 := ⟨denom.size - 1, by omega⟩
        rw [denote, hvsz, ht]; rfl
      have husplit : denote u = denoteN u numer.size
          + (u.getD numer.size 0).toNat * base ^ numer.size := by
        rw [denote, husz]; rfl
      have hutop : (u.getD numer.size 0).toNat < 2 ^ dd.val := by
        have h2 : denote u < 2 ^ dd.val * base ^ numer.size := by
          rw [huval, Nat.mul_comm]
          exact (Nat.mul_lt_mul_left h2d).mpr hNlt
        exact Nat.lt_of_mul_lt_mul_right (a := base ^ numer.size) (by omega)
      -- run the inner division
      obtain ⟨u', q, hres⟩ : ∃ u' q,
          (if denom.size = 1 then div1 u (v.getD (v.size - 1) 0) hnzv else divN u v hnzv) = (u', q) := ⟨_, _, rfl⟩
      have hmain : q.size = numer.size - denom.size + 1 ∧
          denote q = denote u / denote v ∧
          denoteN u' denom.size = denote u % denote v := by
        by_cases h1 : denom.size = 1
        · rw [show (if denom.size = 1 then div1 u (v.getD (v.size - 1) 0) hnzv else divN u v hnzv)
              = div1 u (v.getD (v.size - 1) 0) hnzv from by simp [h1]] at hres
          have hvi : v.size - 1 = 0 := by omega
          have hv0 : 2147483648 ≤ (v.getD (v.size - 1) 0).toNat := by
            rw [hvi, show (0 : Nat) = denom.size - 1 from by omega]; exact hvnorm
          have hvd : 0 < (v.getD (v.size - 1) 0).toNat := by omega
          have hvdD : denote v = (v.getD (v.size - 1) 0).toNat := by
            simp [denote, hvsz, h1, denoteN]
          obtain ⟨g1, g2, g3⟩ := div1_spec u (v.getD (v.size - 1) 0) hvd (by omega)
            (by have hh : u.size - 1 = numer.size := by omega
                rw [hh]; omega)
          rw [hres] at g1 g2 g3
          dsimp only at g1 g2 g3
          rw [← denote] at g3
          obtain ⟨e1, e2⟩ := div_mod_of_eq (V := (v.getD (v.size - 1) 0).toNat) hvd g3 g1
          rw [← hvdD] at e1 e2
          refine ⟨by rw [g2, husz, h1]; omega, e1, ?_⟩
          simp [h1, denoteN, denoteN, ← e2]
        · rw [show (if denom.size = 1 then div1 u (v.getD (v.size - 1) 0) hnzv else divN u v hnzv)
              = divN u v hnzv from by simp [h1]] at hres
          have hvk : v.size = (denom.size - 2) + 2 := by rw [hvsz]; omega
          have hidx : denom.size - 2 + 1 = denom.size - 1 := by omega
          have hnorm2 : base ≤ 2 * (v.getD (denom.size - 2 + 1) 0).toNat := by
            rw [hidx]; simp only [base_eq]; omega
          have hbnd : denote u < denote v * base ^ (u.size - v.size) := by
            have hb1 : (v.getD (denom.size - 1) 0).toNat * base ^ (denom.size - 1) ≤ denote v := by
              omega
            have hb2 : 2147483648 * base ^ (denom.size - 1) ≤ denote v :=
              Nat.le_trans (Nat.mul_le_mul_right _ hvnorm) hb1
            have hb3 : denote v * base ^ (u.size - v.size)
                ≥ 2147483648 * base ^ (denom.size - 1) * base ^ (u.size - v.size) :=
              Nat.mul_le_mul_right _ hb2
            have hb4 : base ^ (denom.size - 1) * base ^ (u.size - v.size) = base ^ numer.size := by
              rw [← Nat.pow_add]; congr 1; omega
            have hb5 : denote u < 2147483648 * base ^ numer.size := by
              rw [huval]
              calc denote numer * 2 ^ dd.val ≤ denote numer * 2147483648 :=
                    Nat.mul_le_mul_left _ hdle
                _ < base ^ numer.size * 2147483648 := (Nat.mul_lt_mul_right (by omega)).mpr hNlt
                _ = 2147483648 * base ^ numer.size := Nat.mul_comm ..
            have hb6 : 2147483648 * base ^ (denom.size - 1) * base ^ (u.size - v.size)
                = 2147483648 * base ^ numer.size := by rw [Nat.mul_assoc, hb4]
            omega
          obtain ⟨g0, g1, g2, g3⟩ := divN_spec u v (denom.size - 2) hvk hnorm2 (by omega) hbnd
          rw [hres] at g0 g1 g2 g3
          dsimp only at g0 g1 g2 g3
          obtain ⟨e1, e2⟩ := div_mod_of_eq hVpos' g3 g2
          have hhz : ∀ i, denom.size ≤ i → u'.getD i 0 = 0 := by
            intro i hi
            have hlt : denote u' < base ^ denom.size :=
              Nat.lt_trans g2 (by rw [← hvsz]; exact denoteN_lt v v.size)
            rcases Nat.eq_zero_or_pos (u'.getD i 0).toNat with h | h
            · exact UInt32.toNat_inj.mp (by rw [h]; rfl)
            · exfalso
              have hge : base ^ i ≤ denote u' := by
                have h1 : 1 * base ^ i ≤ (u'.getD i 0).toNat * base ^ i :=
                  Nat.mul_le_mul_right _ (by omega)
                have h2 : (u'.getD i 0).toNat * base ^ i ≤ denoteN u' (i+1) := by
                  rw [denoteN]; omega
                have h3 : denoteN u' (i+1) ≤ denote u' := by
                  rcases Nat.lt_or_ge (i+1) u'.size with h' | h'
                  · obtain ⟨K, hK⟩ := denoteN_add_high u' (i+1) u'.size (by omega)
                    rw [denote]; omega
                  · rw [denoteN_of_ge u' h']; exact Nat.le_refl _
                omega
              have : base ^ denom.size ≤ base ^ i :=
                Nat.pow_le_pow_right (by simp [base_eq]) hi
              omega
          refine ⟨by rw [g1, husz, hvsz]; omega, e1, ?_⟩
          rw [← denote_of_high_zero u' (n := denom.size) (by rw [g0, husz]; omega) hhz]
          exact e2
      obtain ⟨hqsz, hqval, hrval⟩ := hmain
      rw [hres]
      constructor
      · rw [show min q.size (numer.size - denom.size + 1) = q.size from by omega,
          denote_copyInto_replicate q (numer.size - denom.size + 1) q.size (by omega),
          ← denote, hqval, huval, hvval, Nat.mul_div_mul_right _ _ h2d]
      · rw [divUnnormalize, denote_shiftRightDigits u' hd32 hden, hrval, huval, hvval,
          Nat.mul_mod_mul_right, Nat.mul_div_cancel _ h2d]

/-! ## Correctness of `mpn_compare`, and the rest of `mpn` -/

/-- The loop above as a recursion, for `compare_eq` to induct over. -/
private def compareLoop (a b : Array Digit) : Nat → Int
  | 0 => 0
  | j+1 =>
    let u_j := a.getD j 0
    let v_j := b.getD j 0
    if u_j > v_j then 1 else if u_j < v_j then -1 else compareLoop a b j

/-- The loop as the descending recursion its proof inducts over. -/
theorem compare_eq (a b : Array Digit) :
    compare a b = compareLoop a b (max a.size b.size) := by
  simp only [compare, Id.run]
  generalize max a.size b.size = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.forIn_cons, compareLoop]
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    split
    · cases h : (List.range n).reverse with
      | nil => rfl
      | cons x xs => simp only [List.forIn_cons]; rfl
    · split
      · cases h : (List.range n).reverse with
        | nil => rfl
        | cons x xs => simp only [List.forIn_cons]; rfl
      · exact ih

/-- Both operands scaled by the same amount: same quotient, remainder scaled. -/
private theorem div_mod_scaled (N D t : Nat) (ht : 0 < t) :
    (N * t) / (D * t) = N / D ∧ (N * t) % (D * t) = (N % D) * t :=
  ⟨Nat.mul_div_mul_right _ _ ht, Nat.mul_mod_mul_right ..⟩

/-- A bigger leading digit outweighs everything below it. -/
private theorem denoteN_lt_of_digit_lt (a b : Array Digit) (n : Nat)
    (h : (a.getD n 0).toNat < (b.getD n 0).toNat) : denoteN a (n+1) < denoteN b (n+1) := by
  have h1 : denoteN a n < base ^ n := denoteN_lt a n
  have h2 : ((a.getD n 0).toNat + 1) * base ^ n ≤ (b.getD n 0).toNat * base ^ n :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : ((a.getD n 0).toNat + 1) * base ^ n
      = (a.getD n 0).toNat * base ^ n + base ^ n := by grind
  have h4 : (b.getD n 0).toNat * base ^ n ≤ denoteN b (n+1) := by rw [denoteN]; omega
  rw [denoteN]
  omega

/-- The scan reports the order of the digits it has seen. -/
theorem compareLoop_spec (a b : Array Digit) (n : Nat) :
    compareLoop a b n =
      if denoteN b n < denoteN a n then 1 else if denoteN a n < denoteN b n then -1 else 0 := by
  induction n with
  | zero => simp [compareLoop, denoteN]
  | succ n ih =>
    have hgt : (a.getD n 0 > b.getD n 0) = ((b.getD n 0).toNat < (a.getD n 0).toNat) := rfl
    have hlt : (a.getD n 0 < b.getD n 0) = ((a.getD n 0).toNat < (b.getD n 0).toNat) := rfl
    rw [compareLoop]
    simp only [hgt, hlt]
    rcases Nat.lt_trichotomy (a.getD n 0).toNat (b.getD n 0).toNat with h | h | h
    · have hd := denoteN_lt_of_digit_lt a b n h
      simp only [show ((b.getD n 0).toNat < (a.getD n 0).toNat) = False from eq_false (by omega),
        show ((a.getD n 0).toNat < (b.getD n 0).toNat) = True from eq_true h,
        show (denoteN b (n+1) < denoteN a (n+1)) = False from eq_false (by omega),
        show (denoteN a (n+1) < denoteN b (n+1)) = True from eq_true hd, ite_true]
    · have hdeq : a.getD n 0 = b.getD n 0 := UInt32.toNat_inj.mp h
      simp [ih, denoteN, hdeq]
    · have hd := denoteN_lt_of_digit_lt b a n h
      omega

/-- `mpn_compare` reports the order of its operands. -/
theorem compare_spec (a b : Array Digit) :
    compare a b = if denote b < denote a then 1 else if denote a < denote b then -1 else 0 := by
  rw [compare_eq, compareLoop_spec, denoteN_of_ge a (Nat.le_max_left ..),
    denoteN_of_ge b (Nat.le_max_right ..)]

theorem base_pow (w : Nat) : base ^ w = 2 ^ (32 * w) := by
  rw [show (base : Nat) = 2 ^ 32 from rfl, ← Nat.pow_mul]

private theorem getD_zeros_append_lt (w i : Nat) (b : Array Digit) (h : i < w) :
    ((Array.replicate w (0 : Digit)) ++ b).getD i 0 = 0 := by
  simp [Array.getElem?_append, h]

private theorem getD_zeros_append_ge (w i : Nat) (b : Array Digit) (h : w ≤ i) :
    ((Array.replicate w (0 : Digit)) ++ b).getD i 0 = b.getD (i - w) 0 := by
  simp [Array.getElem?_append, Nat.not_lt.mpr h]

private theorem denoteN_of_all_zero (c : Array Digit) (n : Nat)
    (h : ∀ i, i < n → c.getD i 0 = 0) : denoteN c n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [denoteN, ih (fun i hi => h i (by omega)), h n (by omega)]; simp

/-- Prepending `w` zero digits multiplies the denotation by `base ^ w`. -/
theorem denote_zeros_append (b : Array Digit) (w : Nat) :
    denote ((Array.replicate w (0 : Digit)) ++ b) = denote b * base ^ w := by
  have hsz : ((Array.replicate w (0 : Digit)) ++ b).size = w + b.size := by simp
  have key : ∀ j, denoteN ((Array.replicate w (0 : Digit)) ++ b) (w + j) = denoteN b j * base ^ w := by
    intro j
    induction j with
    | zero =>
      have hzero : denoteN ((Array.replicate w (0 : Digit)) ++ b) w = 0 :=
        denoteN_of_all_zero _ w (fun i hi => getD_zeros_append_lt w i b hi)
      simpa [denoteN] using hzero
    | succ j ih =>
      rw [show w + (j+1) = (w + j) + 1 by omega, denoteN, ih,
        getD_zeros_append_ge w (w+j) b (by omega), show w + j - w = j by omega, denoteN,
        Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm j w]
  rw [denote, hsz, key b.size, denote]

/-- Digit `i` of a value, read off its denotation. -/
theorem denote_digit (a : Array Digit) (i : Nat) :
    denote a / base ^ i % base = (a.getD i 0).toNat := by
  have hb : base ^ (i+1) = base ^ i * base := Nat.pow_succ base i
  have hlow : denoteN a i < base ^ i := denoteN_lt a i
  rw [← Nat.mod_mul_right_div_self, ← hb, ← denoteN_mod, denoteN,
    Nat.add_mul_div_right _ _ (Nat.pow_pos (by simp [base_eq])), Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- Bit `j` of a value is bit `j % 32` of its digit `j / 32`. -/
theorem testBit_denote (a : Array Digit) (j : Nat) :
    (denote a).testBit j = (a.getD (j / digitBits) 0).toNat.testBit (j % digitBits) := by
  obtain ⟨q, r, hr, hj⟩ : ∃ q r, r < 32 ∧ j = r + 32 * q :=
    ⟨j / 32, j % 32, Nat.mod_lt _ (by omega), by omega⟩
  subst hj
  have hq : (r + 32 * q) / digitBits = q := by simp only [digitBits_eq]; omega
  have hrm : (r + 32 * q) % digitBits = r := by simp only [digitBits_eq]; omega
  rw [hq, hrm, Nat.testBit_add, ← base_pow, ← denote_digit a q,
    show (base : Nat) = 2 ^ 32 from rfl, Nat.testBit_mod_two_pow]
  simp [hr]

private theorem Nat.gcd_step (m n : Nat) : Nat.gcd m n = Nat.gcd n (m % n) := by
  rw [Nat.gcd_comm m n, Nat.gcd_rec n m, Nat.gcd_comm]

private theorem toNat_and_one (p : Digit) : (p &&& 1).toNat = p.toNat % 2 := by simp

end MpnProofs

section MpzModel

/-!
## The `mpz` layer

Every `mpn` specification above takes its preconditions as hypotheses: a
nonempty digit array, a divisor no longer than the dividend, a nonzero leading
divisor digit. `mpz` is what establishes them, by keeping every value in a
normalized shape and by sizing the buffers it hands to `mpn`. Bundling that
shape into a type discharges the preconditions once, structurally, instead of
assuming them at each use.
`pow` is the one routine here that is not a wrapper around `mpn`: it squares and
multiplies through `Num.mul`. `Num.val_pow` covers it, and being a well-founded
recursion on the exponent it terminates by construction, which the loop in
`mpz.cpp` did not for exponents at or above `2^31`.
-/

/--
A digit array in the shape `mpz` keeps it: at least one digit, and no leading
zero digit unless the value is a single zero. `mpz::set` establishes it.
-/
structure Num where
  digits : Array Digit
  size_pos : 0 < digits.size
  top_ne_zero : 1 < digits.size → (digits.getD (digits.size - 1) 0).toNat ≠ 0

/-- The natural number a `Num` denotes. -/
def Num.val (a : Num) : Nat := denote a.digits

theorem size_trim_pos (c : Array Digit) (h : 0 < c.size) : 0 < (trim c).size := by
  generalize hh : trim c = r
  apply Id.of_wp_run_eq hh
  mvcgen invariants
  | inv1 => fun c' => ULift.up c'.size
  | inv2 => ⇓ r => match r with
    | .inl c' => spred(⌜0 < c'.size⌝)
    | .inr c' => spred(⌜0 < c'.size⌝)
  all_goals simp_all [Array.size_pop] <;> omega

theorem trim_top_ne_zero (c : Array Digit) :
    1 < (trim c).size → ((trim c).getD ((trim c).size - 1) 0).toNat ≠ 0 := by
  generalize hh : trim c = r
  apply Id.of_wp_run_eq hh
  mvcgen invariants
  | inv1 => fun c' => ULift.up c'.size
  | inv2 => ⇓ r => match r with
    | .inl c' => spred(⌜True⌝)
    | .inr c' => spred(⌜1 < c'.size → (c'.getD (c'.size - 1) 0).toNat ≠ 0⌝)
  all_goals first
    | grind
    | (simp_all [Array.size_pop] <;> omega)

/--
`mpz::set`, which normalizes a magnitude by dropping leading zero digits, keeping
at least one:
```
void mpz::set(size_t sz, mpn_digit const * digits) {
    while (sz > 1 && digits[sz - 1] == 0)
        sz--;
    if (sz != m_size) {
        mpz_dealloc(m_digits, sizeof(mpn_digit)*m_size);
        allocate(sz);
    }
    memcpy(m_digits, digits, sizeof(mpn_digit)*sz);
}
```
The reallocation and `memcpy` are memory management for the buffer `mpz` owns; a
value model has no owned buffer, so `trim` produces the normalized array
directly, the same reason `mpn`'s caller-supplied buffers are not modelled.
-/
def Num.ofArray (a : Array Digit) (h : 0 < a.size) : Num :=
  ⟨trim a, size_trim_pos a h, trim_top_ne_zero a⟩

@[simp] theorem Num.val_ofArray (a : Array Digit) (h : 0 < a.size) :
    (Num.ofArray a h).val = denote a := denote_trim a

/-- A normalized value below `base ^ (size - 1)` can only be a single zero. -/
theorem Num.pow_le_val (a : Num) (h : 1 < a.digits.size) :
    base ^ (a.digits.size - 1) ≤ a.val := by
  obtain ⟨t, ht⟩ : ∃ t, a.digits.size = t + 1 := ⟨a.digits.size - 1, by omega⟩
  have hval : a.val = denoteN a.digits t + (a.digits.getD t 0).toNat * base ^ t := by
    rw [Num.val, denote, ht]; rfl
  have htop : (a.digits.getD t 0).toNat ≠ 0 := by
    have := a.top_ne_zero h
    rwa [show a.digits.size - 1 = t from by omega] at this
  have h1 : 1 * base ^ t ≤ (a.digits.getD t 0).toNat * base ^ t :=
    Nat.mul_le_mul_right _ (by omega)
  grind

theorem Num.val_lt (a : Num) : a.val < base ^ a.digits.size := denoteN_lt a.digits a.digits.size

/-- Normalization makes the digit count monotone in the value. -/
theorem Num.size_le_of_val_le (a b : Num) (h : a.val ≤ b.val) :
    a.digits.size ≤ b.digits.size := by
  rcases Nat.lt_or_ge b.digits.size a.digits.size with hs | hs
  · exfalso
    rcases Nat.lt_or_ge 1 a.digits.size with h1 | h1
    · have hb : b.val < base ^ b.digits.size := b.val_lt
      have ha : base ^ (a.digits.size - 1) ≤ a.val := a.pow_le_val h1
      have hmono : base ^ b.digits.size ≤ base ^ (a.digits.size - 1) :=
        Nat.pow_le_pow_right (by simp [base_eq]) (by omega)
      omega
    · have h2 := a.size_pos
      have h3 := b.size_pos
      omega
  · exact hs

/-- A nonzero normalized value has a nonzero leading digit. -/
theorem Num.top_pos (a : Num) (h : a.val ≠ 0) :
    0 < (a.digits.getD (a.digits.size - 1) 0).toNat := by
  rcases Nat.lt_or_ge 1 a.digits.size with h1 | h1
  · have := a.top_ne_zero h1; omega
  · have hsz : a.digits.size = 1 := by have := a.size_pos; omega
    have : a.val = (a.digits.getD 0 0).toNat := by rw [Num.val, denote, hsz]; simp [denoteN]
    grind
theorem size_add_pos (a b : Array Digit) : 0 < (Mpn.add a b).size := by
  exact size_trim_pos _ (by simp)

theorem size_div_quot (numer denom : Array Digit) (hden : 0 < denom.size)
    (hsz : denom.size ≤ numer.size)
    (htop : 0 < (denom.getD (denom.size - 1) 0).toNat) :
    (div numer denom hden hsz htop).1.size = numer.size - denom.size + 1 := by
  simp [div, show ¬ (numer.size < denom.size) from by omega]
  split <;> rename_i hB
  · grind
  · split <;> rename_i hC
    · simp
    · simp [size_copyInto]

theorem size_div_rem (numer denom : Array Digit) (hden : 0 < denom.size)
    (hsz : denom.size ≤ numer.size)
    (htop : 0 < (denom.getD (denom.size - 1) 0).toNat) :
    (div numer denom hden hsz htop).2.size = denom.size := by
  simp [div, show ¬ (numer.size < denom.size) from by omega]
  split <;> rename_i hB
  · grind
  · split <;> rename_i hC
    · simp
    · simp [divUnnormalize, size_shiftRightDigits]

/-! ### The operations `mpz` builds on `mpn` -/

/--
`cmp` compares two `mpz` by sign; on the non-negative values a `Num` holds it reduces to `mpn_compare`:
```
int cmp(mpz const & a, mpz const & b) {
    if (a.m_sign) {
        if (b.m_sign) {
            return mpn_compare(b.m_digits, b.m_size, a.m_digits, a.m_size);
        } else {
            return -1; // `a` is negative and `b` is nonnegative
        }
    } else {
        if (b.m_sign) {
            return 1; // `a` is nonnegative and `b` is negative
        } else {
            return mpn_compare(a.m_digits, a.m_size, b.m_digits, b.m_size);
        }
    }
}
```
`operator<` and its siblings are `cmp` against zero, which is how `mpz::add`
orders its operands and how `lean_nat_big_le` compares two `mpz`.
-/
def Num.compare (a b : Num) : Int := Mpn.compare a.digits b.digits

/--
`mpz::operator+=` adds two `mpz`; on non-negative values it takes the `m_sign == sign` arm:
```
        size_t new_sz = std::max(m_size, sz)+1;
        size_t real_sz;
        tmp.ensure_capacity(new_sz);
        mpn_add(m_digits, m_size, digits, sz, tmp.begin(), new_sz, &real_sz);
        set(real_sz, tmp.begin());
```
-/
def Num.add (a b : Num) : Num := Num.ofArray (Mpn.add a.digits b.digits) (size_add_pos ..)

/--
`mpz::mul` multiplies two `mpz`; a `Num` exercises only its non-negative case:
```
    size_t new_sz = m_size + sz;
    tmp.ensure_capacity(new_sz);
    mpn_mul(m_digits, m_size, digits, sz, tmp.begin());
    set(new_sz, tmp.begin());
```
-/
def Num.mul (a b : Num) : Num :=
  Num.ofArray (Mpn.mul a.digits b.digits) (by rw [size_mul]; have := a.size_pos; omega)

/--
At the `mpz` layer, `Nat.sub` goes through `mpz::operator-=`, which is `add`
with the operand's sign flipped:
```
mpz & mpz::operator-=(mpz const & o) {
    return add(!o.m_sign, o.m_size, o.m_digits);
}
```
so a difference of two non-negative values takes `add`'s opposite-sign arm:
```
        int r = mpn_compare(m_digits, m_size, digits, sz);
        if (r == 0) {
            operator=(0);
            return *this;
        } else if (r < 0) {
            size_t new_sz = sz;
            tmp.ensure_capacity(new_sz);
            mpn_sub(digits, sz, m_digits, m_size, tmp.begin(), &borrow);
            lean_assert(borrow==0);
            m_sign = sign;
            set(new_sz, tmp.begin());
        } else {
            size_t new_sz = m_size;
            tmp.ensure_capacity(new_sz);
            mpn_sub(m_digits, m_size, digits, sz, tmp.begin(), &borrow);
            lean_assert(borrow == 0);
            set(new_sz, tmp.begin());
        }
```
The `r < 0` arm is where the result would go negative and `m_sign` is set;
`lean_nat_big_sub` clamps that case to zero instead, which is what `Nat`
subtraction does and what this returns.
-/
def Num.sub (a b : Num) : Num :=
  if Mpn.compare a.digits b.digits ≤ 0 then ⟨#[0], by simp, by simp⟩
  else Num.ofArray (Mpn.sub a.digits b.digits).1 (by
    rw [size_sub]; have := a.size_pos; omega)

/--
`mpz::div` divides two `mpz`; a `Num` exercises only its non-negative case:
```
    if (sz > m_size) {
        operator=(0);
        return *this;
    }
    size_t q_sz = m_size - sz + 1;
    size_t r_sz = sz;
    mpn_div(m_digits, m_size, digits, sz, q1.begin(), r1.begin());
    set(q_sz, q1.begin());
```
-/
def Num.div (a b : Num) (hb : b.val ≠ 0) : Num :=
  if h : a.digits.size < b.digits.size then ⟨#[0], by simp, by simp⟩
  else Num.ofArray (Mpn.div a.digits b.digits b.size_pos (by omega) (Num.top_pos b hb)).1 (by
    rw [size_div_quot _ _ b.size_pos (by omega) (Num.top_pos b hb)]; omega)

/--
`mpz::rem` takes the remainder; on non-negative values it differs from `mpz::div`
only in returning the dividend unchanged for a longer divisor and keeping `r1`:
```
    if (sz > m_size) {
        return *this;
    }
    mpn_div(m_digits, m_size, digits, sz, q1.begin(), r1.begin());
    set(r_sz, r1.begin());
```
-/
def Num.mod (a b : Num) (hb : b.val ≠ 0) : Num :=
  if h : a.digits.size < b.digits.size then a
  else Num.ofArray (Mpn.div a.digits b.digits b.size_pos (by omega) (Num.top_pos b hb)).2 (by
    rw [size_div_rem _ _ b.size_pos (by omega) (Num.top_pos b hb)]; exact b.size_pos)

theorem Num.val_mod (a b : Num) (hb : b.val ≠ 0) : (a.mod b hb).val = a.val % b.val := by
  rw [Num.mod]
  split <;> rename_i h
  · have hlt : a.val < b.val := by
      rcases Nat.lt_or_ge a.val b.val with h2 | h2
      · exact h2
      · exact absurd (Num.size_le_of_val_le b a h2) (by omega)
    rw [Nat.mod_eq_of_lt hlt]
  · rw [Num.val_ofArray]
    exact (div_spec a.digits b.digits b.size_pos (by omega) (b.top_pos hb)).2

/-! ### Shifts, as `mpz` implements them -/

/--
`mpz::is_zero()`, which on the GMP-free path is exactly the shape a normalized
value has:
```
    bool is_zero() const {
        return m_size == 1 && m_digits[0] == 0;
    }
```
-/
def Num.isZero (a : Num) : Bool := a.digits.size = 1 && a.digits.getD 0 0 == 0

/--
`mul2k`: shift left by `k` bits, then normalize:
```
    unsigned word_shift  = k / (8 * sizeof(mpn_digit));
    unsigned bit_shift   = k % (8 * sizeof(mpn_digit));
    size_t   new_sz      = old_sz + word_shift + 1;
    for (size_t i = 0; i < word_shift; i++) ds.push_back(0);
    for (size_t i = 0; i < old_sz; i++) ds.push_back(b.m_digits[i]);
    ds.push_back(0);
    if (bit_shift > 0) {
        unsigned comp_shift = (8 * sizeof(mpn_digit)) - bit_shift;
        mpn_digit prev = 0;
        for (size_t i = word_shift; i < new_sz; i++) {
            mpn_digit new_prev = (ds[i] >> comp_shift);
            ds[i] <<= bit_shift;
            ds[i] |= prev;
            prev = new_prev;
        }
    }
    a.set(new_sz, ds.begin());
```
NOTE: that loop carries the bits it displaces forward in `prev`, where
`div_normalize` reads them back out of `a[i-1]`. The two write the same digits,
so `shiftLeftDigits` serves both, but only one of the two shapes appears here.
-/
def Num.shiftLeft (a : Num) (k : Nat) : Num :=
  if k = 0 || a.isZero then a
  else
    Num.ofArray
      (shiftLeftDigits ((Array.replicate (k / digitBits) 0) ++ a.digits)
        (k % digitBits) (a.digits.size + k / digitBits + 1)
        (Nat.mod_lt _ (by simp [digitBits_eq])))
      (by rw [size_shiftLeftDigits]; exact Nat.succ_pos _)

/--
`div2k`: shift right by `k` bits, then normalize:
```
    unsigned digit_shift = k / (8 * sizeof(mpn_digit));
    if (digit_shift >= b.m_size) {
        a = 0;
        return;
    }
    size_t new_sz       = sz - digit_shift;
    unsigned bit_shift  = k % (8 * sizeof(mpn_digit));
    unsigned comp_shift = (8 * sizeof(mpn_digit)) - bit_shift;
    digit_buffer ds;
    ds.append(b.m_size, b.m_digits);
    if (new_sz < sz) {
        size_t i       = 0;
        size_t j       = digit_shift;
        if (bit_shift != 0) {
            for (; i < new_sz - 1; i++, j++) {
                ds[i] = ds[j];
                ds[i] >>= bit_shift;
                ds[i] |= (ds[j+1] << comp_shift);
            }
            ds[i] = ds[j];
            ds[i] >>= bit_shift;
        }
        else {
            for (; i < new_sz; i++, j++) {
                ds[i] = ds[j];
            }
        }
    }
    else {
        size_t i = 0;
        for (; i < new_sz - 1; i++) {
            ds[i] >>= bit_shift;
            ds[i] |= (ds[i+1] << comp_shift);
        }
        ds[i] >>= bit_shift;
    }
    a.set(new_sz, ds.begin());
```
NOTE: the two arms differ only in whether the digits are moved down by
`digit_shift` as they are shifted; both write what `shiftRightDigits` writes,
applied to the digits from `digit_shift` up.
-/
def Num.shiftRight (a : Num) (k : Nat) : Num :=
  if k = 0 || a.isZero then a
  else if h : a.digits.size ≤ k / digitBits then ⟨#[0], by simp, by simp⟩
  else
    Num.ofArray
      (shiftRightDigits (a.digits.extract (k / digitBits) a.digits.size)
        (k % digitBits) (a.digits.size - k / digitBits) (Nat.mod_lt _ (by simp [digitBits_eq])))
      (by rw [size_shiftRightDigits]; omega)

/-- Any digit array as a `Num`, for building test values. -/
def Num.ofArray! (a : Array Digit) : Num :=
  if h : 0 < a.size then Num.ofArray a h else ⟨#[0], by simp, by simp⟩

/-! ### Bitwise operations, as `mpz` implements them -/

/--
`mpz::operator&=` and friends, which combine digits pointwise over the longer
length, reading absent digits as zero:
```
    size_t sz = std::max(m_size, o.m_size);
    for (size_t i = 0; i < sz; i++) {
        mpn_digit u_i = (i < m_size)   ? m_digits[i]   : 0;
        mpn_digit v_i = (i < o.m_size) ? o.m_digits[i] : 0;
        r.push_back(u_i & v_i);
    }
    set(sz, r.begin());
```
`operator|=` and `operator^=` are the same function with `|` and `^` in place of
`&`, which is why one definition parameterized by the digit operation covers all
three.
-/
def bitwiseDigits (f : Digit → Digit → Digit) (a b : Array Digit) : Array Digit := Id.run do
  let sz := max a.size b.size
  let mut r : Array Digit := #[]
  for i in List.range sz do
    let u_i := a.getD i 0
    let v_i := b.getD i 0
    r := r.push (f u_i v_i)
  return r

/-- The loop fills `max a.size b.size` digits, each `f (a[i]) (b[i])`. -/
theorem bitwiseDigits_spec (f : Digit → Digit → Digit) (a b : Array Digit) :
    (bitwiseDigits f a b).size = max a.size b.size ∧
    ∀ i, i < max a.size b.size → (bitwiseDigits f a b).getD i 0 = f (a.getD i 0) (b.getD i 0) := by
  generalize h : bitwiseDigits f a b = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => ⇓ (xs, r) => spred(⌜r.size = xs.prefix.length ∧
      ∀ i, i < xs.prefix.length → r.getD i 0 = f (a.getD i 0) (b.getD i 0)⌝)
  case vc1.step =>
    obtain ⟨hsz, hval⟩ := ‹_ ∧ _›
    have hc := range_split_index ‹List.range _ = _ ++ _ :: _›
    subst hc
    refine ⟨by grind, ?_⟩
    intro i hi
    rw [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [getD_push_lt _ _ (by omega), hval i h]
    · subst h; rw [← hsz, getD_push_eq]
  all_goals (intros; first | grind | simp_all)

@[simp] theorem size_bitwiseDigits (f : Digit → Digit → Digit) (a b : Array Digit) :
    (bitwiseDigits f a b).size = max a.size b.size := (bitwiseDigits_spec f a b).1

/-- `mpz::operator&=`. -/
def Num.land (a b : Num) : Num :=
  Num.ofArray (bitwiseDigits (· &&& ·) a.digits b.digits)
    (by rw [size_bitwiseDigits]; have := a.size_pos; omega)

/-- `mpz::operator|=`. -/
def Num.lor (a b : Num) : Num :=
  Num.ofArray (bitwiseDigits (· ||| ·) a.digits b.digits)
    (by rw [size_bitwiseDigits]; have := a.size_pos; omega)

/-- `mpz::operator^=`. -/
def Num.xor (a b : Num) : Num :=
  Num.ofArray (bitwiseDigits (· ^^^ ·) a.digits b.digits)
    (by rw [size_bitwiseDigits]; have := a.size_pos; omega)

/-! ### `gcd`, as `mpz` implements it -/

/--
Euclid's loop, as `gcd` in `mpz.cpp` runs it:
```
        while (true) {
            aux = rem(tmp1, tmp2);
            if (aux.is_zero()) {
                swap(g, tmp2);
                break;
            }
            swap(tmp1, tmp2);
            swap(tmp2, aux);
        }
```
It terminates because the remainder is below the divisor, which is what the
`termination_by` below records.
-/
def Num.gcdLoop (a b : Num) : Num :=
  if h : b.val = 0 then a else Num.gcdLoop b (a.mod b h)
termination_by b.val
decreasing_by
  rw [Num.val_mod a b h]
  exact Nat.mod_lt _ (by omega)

/--
`gcd`: order the operands, then run Euclid:
```
    if (tmp1 < tmp2)
        swap(tmp1, tmp2);
    if (tmp2.is_zero()) {
        swap(g, tmp1);
    } else { ... }
```
-/
def Num.gcd (a b : Num) : Num :=
  if Mpn.compare a.digits b.digits < 0 then Num.gcdLoop b a else Num.gcdLoop a b

/-- `mpz(1)`. -/
def Num.one : Num := ⟨#[1], by simp, by simp⟩

private theorem toNat_shiftRight_one (p : Digit) : (p >>> 1).toNat = p.toNat / 2 := rfl

/-- `if (p & 1) result *= power;`, the conditional multiply in `mpz::pow`. -/
def Num.powMul (power result : Num) (p : Digit) : Num :=
  if p &&& 1 = 1 then result.mul power else result

/--
The `while` loop of `mpz::pow` below, with `power` and `result` as parameters so
that `val_powLoop` can induct on the exponent:
```
    while (p != 0) {
        if (p & 1)
            result *= power;
        p >>= 1;
        if (p != 0)
            power *= power;
    }
```
The exponent's bits are consumed from the bottom, `power` multiplied into
`result` where a bit is set and squared for the next bit. The final squaring is
skipped once the remaining exponent is zero.
-/
def Num.powLoop (power result : Num) (p : Digit) : Num :=
  if p = 0 then result
  else if p >>> 1 = 0 then Num.powMul power result p
  else Num.powLoop (power.mul power) (Num.powMul power result p) (p >>> 1)
termination_by p.toNat
decreasing_by
  rename_i hne _
  rw [toNat_shiftRight_one]
  have : p.toNat ≠ 0 := fun h0 => hne (UInt32.toNat_inj.mp (by rw [h0]; rfl))
  omega

/--
`mpz::pow`, square and multiply:
```
mpz mpz::pow(unsigned int p) const {
    mpz power(*this);
    mpz result(1);
    while (p != 0) { ... }
    return result;
}
```
-/
def Num.pow (a : Num) (p : Digit) : Num := Num.powLoop a Num.one p

end MpzModel

section MpzProofs

@[simp] theorem Num.val_add (a b : Num) : (a.add b).val = a.val + b.val := by
  rw [Num.add, Num.val_ofArray, denote_add, Num.val, Num.val]

@[simp] theorem Num.val_ofArray! (a : Array Digit) (h : 0 < a.size) :
    (Num.ofArray! a).val = denote a := by
  unfold Num.ofArray!
  split <;> rename_i h2
  · exact Num.val_ofArray a h2
  · exact absurd h h2

@[simp] theorem Num.val_one : Num.one.val = 1 := denote_singleton 1


/-!
## Proofs for the `mpz` layer
-/

theorem Num.compare_spec (a b : Num) :
    a.compare b = if b.val < a.val then 1 else if a.val < b.val then -1 else 0 :=
  Mpn.compare_spec a.digits b.digits

@[simp] theorem Num.val_mul (a b : Num) : (a.mul b).val = a.val * b.val := by
  rw [Num.mul, Num.val_ofArray, denote_mul, Num.val, Num.val]

@[simp] theorem Num.val_sub (a b : Num) : (a.sub b).val = a.val - b.val := by
  have hc : Mpn.compare a.digits b.digits
      = if b.val < a.val then 1 else if a.val < b.val then -1 else 0 := Num.compare_spec a b
  rw [Num.sub]
  split <;> rename_i h
  · -- the guard says the difference would be negative, so the result is zero
    show denote #[0] = _
    rw [denote_singleton, show ((0 : Digit)).toNat = 0 from rfl]
    omega
  · have hlt : b.val < a.val := by
      rcases Nat.lt_or_ge b.val a.val with hlt | hle
      · exact hlt
      · omega
    -- with `b` below `a` the subtraction cannot borrow out of the top digit
    have hd := denote_sub a.digits b.digits
    have hlen : (Mpn.sub a.digits b.digits).1.size = max a.digits.size b.digits.size := size_sub ..
    have hsmall : denote (Mpn.sub a.digits b.digits).1
        < base ^ (max a.digits.size b.digits.size) := by
      rw [denote, hlen]; exact denoteN_lt _ _
    simp only [Num.val] at hlt
    have hb0 : (Mpn.sub a.digits b.digits).2.toNat = 0 := by
      rcases Nat.eq_zero_or_pos (Mpn.sub a.digits b.digits).2.toNat with h0 | h0
      · exact h0
      · exfalso
        have hge : base ^ (max a.digits.size b.digits.size)
            ≤ (Mpn.sub a.digits b.digits).2.toNat * base ^ (max a.digits.size b.digits.size) :=
          Nat.le_mul_of_pos_left _ h0
        omega
    rw [hb0] at hd
    rw [Num.val_ofArray]
    simp only [Num.val]
    omega

theorem Num.val_div (a b : Num) (hb : b.val ≠ 0) : (a.div b hb).val = a.val / b.val := by
  rw [Num.div]
  split <;> rename_i h
  · have hlt : a.val < b.val := by
      rcases Nat.lt_or_ge a.val b.val with h2 | h2
      · exact h2
      · exact absurd (Num.size_le_of_val_le b a h2) (by omega)
    rw [Nat.div_eq_of_lt hlt]
    rfl
  · rw [Num.val_ofArray]
    exact (div_spec a.digits b.digits b.size_pos (by omega) (b.top_pos hb)).1

theorem Num.val_isZero (a : Num) (h : a.isZero) : a.val = 0 := by
  simp only [Num.isZero, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp [Num.val, denote, h.1, denoteN, h.2]

/-- `mul2k` shifts left: it multiplies by `2^k`. -/
theorem Num.val_shiftLeft (a : Num) (k : Nat) : (a.shiftLeft k).val = a.val * 2 ^ k := by
  rw [Num.shiftLeft]
  split <;> rename_i h
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · simp [h]
    · simp [Num.val_isZero a h]
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    have hbit : k % digitBits < digitBits := Nat.mod_lt _ (by simp [digitBits_eq])
    have hpad : denote ((Array.replicate (k / digitBits) (0 : Digit)) ++ a.digits)
        = a.val * base ^ (k / digitBits) := denote_zeros_append a.digits _
    have hfit : denote ((Array.replicate (k / digitBits) (0 : Digit)) ++ a.digits)
        * 2 ^ (k % digitBits) < base ^ (a.digits.size + k / digitBits + 1) := by
      have h1 : a.val < base ^ a.digits.size := a.val_lt
      have h2 : (2:Nat) ^ (k % digitBits) ≤ base := by
        calc (2:Nat) ^ (k % digitBits) ≤ 2 ^ 32 :=
              Nat.pow_le_pow_right (by omega) (by simp only [digitBits_eq] at hbit ⊢; omega)
          _ = base := rfl
      calc denote ((Array.replicate (k / digitBits) (0 : Digit)) ++ a.digits)
            * 2 ^ (k % digitBits)
          = a.val * base ^ (k / digitBits) * 2 ^ (k % digitBits) := by grind
        _ < base ^ a.digits.size * base ^ (k / digitBits) * 2 ^ (k % digitBits) := by
            refine (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr ?_
            exact (Nat.mul_lt_mul_right (Nat.pow_pos (by simp [base_eq]))).mpr h1
        _ ≤ base ^ a.digits.size * base ^ (k / digitBits) * base :=
            Nat.mul_le_mul_left _ h2
        _ = base ^ (a.digits.size + k / digitBits + 1) := by
            rw [← Nat.pow_add, ← Nat.pow_succ]
    rw [Num.val_ofArray,
      denote_shiftLeftDigits _ hbit (by simp; omega) hfit, hpad, Nat.mul_assoc,
      base_pow, ← Nat.pow_add]
    congr 2
    simp only [digitBits_eq]
    omega

/-- `div2k` shifts right: it divides by `2^k`. -/
theorem Num.val_shiftRight (a : Num) (k : Nat) : (a.shiftRight k).val = a.val / 2 ^ k := by
  have hbit : k % digitBits < digitBits := Nat.mod_lt _ (by simp [digitBits_eq])
  have hk : 32 * (k / digitBits) + k % digitBits = k := by
    simp only [digitBits_eq]; omega
  rw [Num.shiftRight]
  split <;> rename_i h
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · simp [h]
    · simp [Num.val_isZero a h]
  · split <;> rename_i h2
    · -- the shift clears every digit
      refine (Nat.div_eq_of_lt ?_).symm
      have h1 : a.val < base ^ a.digits.size := a.val_lt
      have h3 : base ^ a.digits.size ≤ 2 ^ k := by
        rw [base_pow]
        exact Nat.pow_le_pow_right (by omega) (by simp only [digitBits_eq] at h2 ⊢; omega)
      omega
    · -- the general case: drop `k / 32` digits, then shift the rest
      have hw : k / digitBits ≤ a.digits.size := by omega
      have hext : (a.digits.extract (k / digitBits) a.digits.size).size
          = a.digits.size - k / digitBits := by simp
      have hsplit : a.val = denoteN a.digits (k / digitBits)
          + denote (a.digits.extract (k / digitBits) a.digits.size) * base ^ (k / digitBits) := by
        exact denoteN_extract (j := k / digitBits) a.digits a.digits.size hw (Nat.le_refl _)
      have hlow : denoteN a.digits (k / digitBits) < base ^ (k / digitBits) :=
        denoteN_lt a.digits _
      have hdiv : a.val / base ^ (k / digitBits)
          = denote (a.digits.extract (k / digitBits) a.digits.size) := by
        rw [hsplit, Nat.add_mul_div_right _ _ (Nat.pow_pos (by simp [base_eq])),
          Nat.div_eq_of_lt hlow, Nat.zero_add]
      rw [Num.val_ofArray,
        denote_shiftRightDigits _ hbit (by omega),
        show denoteN (a.digits.extract (k / digitBits) a.digits.size)
            (a.digits.size - k / digitBits)
          = denote (a.digits.extract (k / digitBits) a.digits.size) from by
            rw [denote, hext],
        ← hdiv, Nat.div_div_eq_div_mul, base_pow, ← Nat.pow_add, hk]

private theorem getD_bitwiseDigits (f : Digit → Digit → Digit) (hf : f 0 0 = 0)
    (a b : Array Digit) (i : Nat) :
    (bitwiseDigits f a b).getD i 0 = f (a.getD i 0) (b.getD i 0) := by
  rcases Nat.lt_or_ge i (max a.size b.size) with h | h
  · exact (bitwiseDigits_spec f a b).2 i h
  · rw [getD_of_ge _ (by rw [size_bitwiseDigits]; omega), getD_of_ge a (by omega),
      getD_of_ge b (by omega), hf]

theorem denote_bitwiseDigits_and (a b : Array Digit) :
    denote (bitwiseDigits (· &&& ·) a b) = denote a &&& denote b := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_denote, getD_bitwiseDigits _ (by decide) a b, UInt32.toNat_and,
    Nat.testBit_and, Nat.testBit_and, testBit_denote, testBit_denote]

theorem denote_bitwiseDigits_or (a b : Array Digit) :
    denote (bitwiseDigits (· ||| ·) a b) = denote a ||| denote b := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_denote, getD_bitwiseDigits _ (by decide) a b, UInt32.toNat_or,
    Nat.testBit_or, Nat.testBit_or, testBit_denote, testBit_denote]

theorem denote_bitwiseDigits_xor (a b : Array Digit) :
    denote (bitwiseDigits (· ^^^ ·) a b) = denote a ^^^ denote b := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_denote, getD_bitwiseDigits _ (by decide) a b, UInt32.toNat_xor,
    Nat.testBit_xor, Nat.testBit_xor, testBit_denote, testBit_denote]

@[simp] theorem Num.val_land (a b : Num) : (a.land b).val = a.val &&& b.val := by
  rw [Num.land, Num.val_ofArray, denote_bitwiseDigits_and, Num.val, Num.val]

@[simp] theorem Num.val_lor (a b : Num) : (a.lor b).val = a.val ||| b.val := by
  rw [Num.lor, Num.val_ofArray, denote_bitwiseDigits_or, Num.val, Num.val]

@[simp] theorem Num.val_xor (a b : Num) : (a.xor b).val = a.val ^^^ b.val := by
  rw [Num.xor, Num.val_ofArray, denote_bitwiseDigits_xor, Num.val, Num.val]

theorem Num.val_gcdLoop (a b : Num) : (a.gcdLoop b).val = Nat.gcd a.val b.val := by
  rw [Num.gcdLoop]
  split <;> rename_i h
  · simp [h]
  · rw [Num.val_gcdLoop b (a.mod b h), Num.val_mod a b h, ← Nat.gcd_step]
termination_by b.val
decreasing_by
  rename_i h
  rw [Num.val_mod a b h]
  exact Nat.mod_lt _ (by omega)

/-- `gcd` computes the greatest common divisor. -/
theorem Num.val_gcd (a b : Num) : (a.gcd b).val = Nat.gcd a.val b.val := by
  rw [Num.gcd]
  split
  · rw [Num.val_gcdLoop, Nat.gcd_comm]
  · rw [Num.val_gcdLoop]

theorem Num.val_powMul (power result : Num) (p : Digit) :
    (Num.powMul power result p).val = result.val * power.val ^ (p.toNat % 2) := by
  rw [Num.powMul]
  split <;> rename_i hb
  · have : p.toNat % 2 = 1 := by rw [← toNat_and_one, hb]; rfl
    rw [this, Num.val_mul, Nat.pow_one]
  · have h1 : (p &&& 1).toNat ≠ 1 := fun hx => hb (UInt32.toNat_inj.mp (by rw [hx]; rfl))
    simp_all

theorem Num.val_powLoop (power result : Num) (p : Digit) :
    (Num.powLoop power result p).val = result.val * power.val ^ p.toNat := by
  rw [Num.powLoop]
  split <;> rename_i h
  · subst h; simp
  · have hp : p.toNat ≠ 0 := fun h0 => h (UInt32.toNat_inj.mp (by rw [h0]; rfl))
    split <;> rename_i h1
    · have h2 : p.toNat / 2 = 0 := by rw [← toNat_shiftRight_one, h1]; rfl
      rw [Num.val_powMul]
      have : p.toNat % 2 = p.toNat := by omega
      rw [this]
    · rw [Num.val_powLoop, Num.val_powMul, toNat_shiftRight_one, Num.val_mul,
        Nat.mul_pow, ← Nat.pow_add, Nat.mul_assoc, ← Nat.pow_add]
      grind
termination_by p.toNat
decreasing_by
  rename_i hne _
  rw [toNat_shiftRight_one]
  have : p.toNat ≠ 0 := fun h0 => hne (UInt32.toNat_inj.mp (by rw [h0]; rfl))
  omega

/-- `pow` raises to a power. It terminates for every exponent, including `2^31`
and above, where the `mpz.cpp` loop this replaces used to spin forever. -/
theorem Num.val_pow (a : Num) (p : Digit) : (a.pow p).val = a.val ^ p.toNat := by
  rw [Num.pow, Num.val_powLoop, Num.val_one, Nat.one_mul]


private theorem compare_le_zero (x y : Num) : (x.compare y ≤ 0) ↔ (x.val ≤ y.val) := by
  rw [Num.compare_spec]
  split <;> rename_i h1
  · omega
  · omega

end MpzProofs

section ObjectModel

/-!
## The `lean_object` layer

`lean_nat_div` and its siblings dispatch on how a `Nat` is represented: a
`size_t` scalar carrying a tag bit, or a pointer to an `mpz`. The `mpz` case
never holds a value small enough to be a scalar, because `mpz_to_nat` re-boxes
anything that fits:
```
static inline obj_res mpz_to_nat(mpz const & m) {
    if (m.is_size_t() && m.get_size_t() <= LEAN_MAX_SMALL_NAT)
        return lean_box(m.get_size_t());
    else
        return mpz_to_nat_core(m);
}
```
The fast paths rely on that invariant without checking it, since `lean_assert`
compiles out of a release build. Bundling it into the type is what makes those
assertions provable here.

Representing the tagged pointer itself would need addresses, so the pointer is
where the transliteration stops: what is modelled is the choice between the two
representations, on a 64-bit target.
-/

/-- `#define LEAN_MAX_SMALL_NAT (SIZE_MAX >> 1)` -/
def maxSmallNat : Nat := 2 ^ 63 - 1

/-- `lean_box(n) = (lean_object*)(((size_t)(n) << 1) | 1)` -/
def box (n : Nat) : UInt64 := (UInt64.ofNat n <<< 1) ||| 1

/-- `lean_unbox(o) = (size_t)(o) >> 1` -/
def unbox (o : UInt64) : Nat := (o >>> 1).toNat

/-- A tagged value is odd, and the tag is the only thing bit 0 carries. -/
private theorem two_mul_or_one (n : Nat) : 2 * n ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.mul_mod_right]
  | succ i => grind

/-- `&` on two tagged values combines the payloads and keeps the tag. -/
private theorem two_mul_add_one_and (m n : Nat) :
    (2 * m + 1) &&& (2 * n + 1) = 2 * (m &&& n) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    have h3 : (2 * (m &&& n) + 1) / 2 = m &&& n := by omega
    simp [Nat.testBit_succ, h1, h2, h3]

/-- `|` on two tagged values, for the same reason. -/
private theorem two_mul_add_one_or (m n : Nat) :
    (2 * m + 1) ||| (2 * n + 1) = 2 * (m ||| n) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    have h3 : (2 * (m ||| n) + 1) / 2 = m ||| n := by omega
    simp [Nat.testBit_succ, h1, h2, h3]

/-- The number a box holds, before the tag is stripped. -/
theorem toNat_box (n : Nat) (h : n ≤ maxSmallNat) : (box n).toNat = 2 * n + 1 := by
  have hn : n < 2 ^ 64 := by simp only [maxSmallNat] at h; omega
  have hlt : 2 * n < 2 ^ 64 := by simp only [maxSmallNat] at h; omega
  have hofNat : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' hn
  have hshift : (UInt64.ofNat n <<< 1).toNat = 2 * n := by
    rw [UInt64.toNat_shiftLeft, hofNat,
      Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt hlt
  rw [box, UInt64.toNat_or, hshift]
  exact two_mul_or_one n

/--
Boxing is injective on the scalar range. The tag costs exactly one bit, which is
why `LEAN_MAX_SMALL_NAT` is `SIZE_MAX >> 1` and not something else: one more and
the shift would overflow.
-/
theorem unbox_box (n : Nat) (h : n ≤ maxSmallNat) : unbox (box n) = n := by
  rw [unbox, UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl,
    toNat_box n h]
  omega

/--
`lean_nat_land`'s fast path never unboxes:
```
        return (lean_object*)((size_t)(a1) & (size_t)(a2));
```
It can do that because the tag bit is set in both operands, so `&` leaves it
set and the payload bits combine on their own.
-/
theorem box_and (m n : Nat) (hm : m ≤ maxSmallNat) (hn : n ≤ maxSmallNat) :
    box m &&& box n = box (m &&& n) := by
  have hmn : m &&& n ≤ maxSmallNat := Nat.le_trans (Nat.and_le_left ..) hm
  refine UInt64.toNat_inj.mp ?_
  rw [UInt64.toNat_and, toNat_box m hm, toNat_box n hn, toNat_box _ hmn]
  exact two_mul_add_one_and m n

/-- `lean_nat_lor`'s fast path, for the same reason as `land`. -/
theorem box_or (m n : Nat) (hm : m ≤ maxSmallNat) (hn : n ≤ maxSmallNat) :
    box m ||| box n = box (m ||| n) := by
  have hmn : m ||| n ≤ maxSmallNat := by
    simp only [maxSmallNat] at *
    exact Nat.lt_succ_iff.mp (Nat.or_lt_two_pow (n := 63) (by omega) (by omega))
  refine UInt64.toNat_inj.mp ?_
  rw [UInt64.toNat_or, toNat_box m hm, toNat_box n hn, toNat_box _ hmn]
  exact two_mul_add_one_or m n

/--
A `Nat` object: a boxed scalar, or an `mpz`. The `big` case is never small
enough to be boxed, which is the invariant `mpz_to_nat` maintains.
-/
inductive NatObj where
  | small (n : Nat) (h : n ≤ maxSmallNat)
  | big (m : Num) (h : maxSmallNat < m.val)

/-- The natural number an object denotes; a reading of the representation, with
no counterpart in the runtime. -/
def NatObj.val : NatObj → Nat
  | .small n _ => n
  | .big m _ => m.val

/-- What `panic!` falls back to; `lean_internal_panic` does not return at all. -/
instance : Inhabited NatObj := ⟨.small 0 (Nat.zero_le _)⟩

/--
`mpz_to_nat`, which re-boxes anything that fits in a scalar:
```
static inline obj_res mpz_to_nat(mpz const & m) {
    if (m.is_size_t() && m.get_size_t() <= LEAN_MAX_SMALL_NAT)
        return lean_box(m.get_size_t());
    else
        return mpz_to_nat_core(m);
}
```
-/
def mpzToNat (m : Num) : NatObj :=
  if h : m.val ≤ maxSmallNat then .small m.val h else .big m (by omega)

/--
`mpz_to_nat_core`, which allocates without re-boxing:
```
object * mpz_to_nat_core(mpz const & m) {
    lean_assert(!m.is_size_t() || m.get_size_t() > LEAN_MAX_SMALL_NAT);
    return alloc_mpz(m);
}
```
Its assertion is the invariant `big` already carries, so it is the constructor.
-/
def mpzToNatCore (m : Num) (h : maxSmallNat < m.val) : NatObj := .big m h

/--
`mpz::of_size_t`, which on a 64-bit target is `init_uint64`:
```
    static mpz of_size_t(size_t v) {
        if (sizeof(size_t) == sizeof(uint64))
            return mpz((uint64) v);
        else
            return mpz((unsigned) v);
    }
```
```
void mpz::init_uint64(uint64 v) {
    m_sign = false;
    if (v <= std::numeric_limits<unsigned>::max()) {
        allocate(1);
        m_digits[0] = v;
    } else {
        allocate(2);
        m_digits[0] = static_cast<mpn_digit>(v);
        m_digits[1] = static_cast<mpn_digit>(v >> 8*sizeof(mpn_digit));
    }
}
```
NOTE: `mpz::init_uint64` branches on whether one digit is enough; this always writes two
and lets `mpz::set`'s trimming drop the second, which leaves the same value in
the same normalized shape.
-/
def Num.ofSizeT (n : Nat) : Num :=
  Num.ofArray! #[UInt32.ofNat (n % base), UInt32.ofNat (n / base)]

@[simp] theorem Num.val_ofSizeT (n : Nat) (h : n < base ^ 2) : (Num.ofSizeT n).val = n := by
  have hbpos : 0 < base := by grind
  have hlo : (UInt32.ofNat (n % base)).toNat = n % base :=
    UInt32.toNat_ofNat_of_lt' (Nat.mod_lt _ hbpos)
  have hhib : n / base < base := by
    rw [Nat.pow_two] at h; exact Nat.div_lt_of_lt_mul (by omega)
  have hhi : (UInt32.ofNat (n / base)).toNat = n / base :=
    UInt32.toNat_ofNat_of_lt' hhib
  have hd : denote #[UInt32.ofNat (n % base), UInt32.ofNat (n / base)]
      = (n % base) + (n / base) * base := by
    have hmod : n / base % base = n / base := Nat.mod_eq_of_lt hhib
    simp only [base_eq] at hmod
    simp [denote, denoteN, hmod]
  rw [Num.ofSizeT, Num.val_ofArray! _ (by simp), hd, Nat.mul_comm]
  exact Nat.mod_add_div n base

/--
`lean_nat_div`, and `lean_nat_big_div` behind it:
```
static inline lean_obj_res lean_nat_div(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t n1 = lean_unbox(a1);
        size_t n2 = lean_unbox(a2);
        if (n2 == 0)
            return lean_box(0);
        else
            return lean_box(n1 / n2);
    } else {
        return lean_nat_big_div(a1, a2);
    }
}
```
```
extern "C" LEAN_EXPORT object * lean_nat_big_div(object * a1, object * a2) {
    lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
    if (lean_is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        lean_assert(mpz::of_size_t(lean_unbox(a1)) / mpz_value(a2) == 0);
        return lean_box(0);
    } else if (lean_is_scalar(a2)) {
        usize n2 = lean_unbox(a2);
        return n2 == 0 ? a2 : mpz_to_nat(mpz_value(a1) / mpz::of_size_t(n2));
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mpz_to_nat(mpz_value(a1) / mpz_value(a2));
    }
}
```
-/
def natDiv : NatObj → NatObj → NatObj
  | .small n₁ h₁, .small n₂ _ =>
    if n₂ = 0 then .small 0 (Nat.zero_le _)
    else .small (n₁ / n₂) (Nat.le_trans (Nat.div_le_self ..) h₁)
  | .small _ _, .big _ _ => .small 0 (Nat.zero_le _)
  | .big m₁ _, .small n₂ h₂ =>
    if h : n₂ = 0 then .small 0 (Nat.zero_le _)
    else mpzToNat (m₁.div (Num.ofSizeT n₂) (by
      rw [Num.val_ofSizeT n₂ (by simp only [maxSmallNat, base_eq] at *; omega)]; exact h))
  | .big m₁ _, .big m₂ h₂ => mpzToNat (m₁.div m₂ (by omega))

/-- The `mpz` an object denotes, which is what `lean_nat_big_*` reads. -/
def NatObj.toNum : NatObj → Num
  | .small n _ => Num.ofSizeT n
  | .big m _ => m

/--
`lean_usize_to_nat`:
```
static inline lean_obj_res lean_usize_to_nat(size_t n) {
    if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT))
        return lean_box(n);
    else
        return lean_big_usize_to_nat(n);
}
```
-/
def usizeToNat (n : Nat) (h64 : n < base ^ 2) : NatObj :=
  if h : n ≤ maxSmallNat then .small n h
  else .big (Num.ofSizeT n) (by rw [Num.val_ofSizeT n h64]; omega)

/--
`lean_nat_add`:
```
static inline LEAN_ALWAYS_INLINE lean_obj_res lean_nat_add(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2)))
        return lean_usize_to_nat(lean_unbox(a1) + lean_unbox(a2));
    else
        return lean_nat_big_add(a1, a2);
}
```
The scalar sum cannot overflow `size_t`: two scalars are at most `2^63 - 1`, so
their sum is below `2^64`. That is the headroom the tag bit leaves, and the
reason this path needs no check.
-/
def natAdd : NatObj → NatObj → NatObj
  | .small n₁ h₁, .small n₂ h₂ =>
    usizeToNat (n₁ + n₂) (by simp only [maxSmallNat, base_eq] at *; omega)
  | .small n₁ _, .big m₂ h₂ =>
    mpzToNatCore ((Num.ofSizeT n₁).add m₂) (by rw [Num.val_add]; omega)
  | .big m₁ h₁, .small n₂ _ =>
    mpzToNatCore (m₁.add (Num.ofSizeT n₂)) (by rw [Num.val_add]; omega)
  | .big m₁ h₁, .big m₂ _ => mpzToNatCore (m₁.add m₂) (by rw [Num.val_add]; omega)

/--
`lean_nat_sub`, which clamps at zero as `Nat` subtraction does:
```
static inline LEAN_ALWAYS_INLINE lean_obj_res lean_nat_sub(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t n1 = lean_unbox(a1);
        size_t n2 = lean_unbox(a2);
        if (n1 < n2)
            return lean_box(0);
        else
            return lean_box(n1 - n2);
    } else {
        return lean_nat_big_sub(a1, a2);
    }
}
```
-/
def natSub : NatObj → NatObj → NatObj
  | .small n₁ h₁, .small n₂ _ =>
    if n₁ < n₂ then .small 0 (Nat.zero_le _) else .small (n₁ - n₂) (by omega)
  | .small _ _, .big _ _ => .small 0 (Nat.zero_le _)
  | .big m₁ _, .small n₂ _ => mpzToNat (m₁.sub (Num.ofSizeT n₂))
  | .big m₁ _, .big m₂ _ =>
    if m₁.val < m₂.val then .small 0 (Nat.zero_le _) else mpzToNat (m₁.sub m₂)

/--
`lean_nat_mul`:
```
static inline LEAN_ALWAYS_INLINE lean_obj_res lean_nat_mul(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t n1 = lean_unbox(a1);
        if (n1 == 0)
            return a1;
        size_t n2 = lean_unbox(a2);
        size_t r  = n1*n2;
        if (r <= LEAN_MAX_SMALL_NAT && r / n1 == n2)
            return lean_box(r);
        else
            return lean_nat_overflow_mul(n1, n2);
    } else {
        return lean_nat_big_mul(a1, a2);
    }
}
```
NOTE: `r / n1 == n2` is there to catch the `size_t` wraparound in `n1*n2`.
`Nat` does not wrap, so the size test alone decides the same branch here.
-/
def natMul : NatObj → NatObj → NatObj
  | .small n₁ _, .small n₂ _ =>
    if n₁ = 0 then .small 0 (Nat.zero_le _)
    else if h : n₁ * n₂ ≤ maxSmallNat then .small (n₁ * n₂) h
    else mpzToNat ((Num.ofSizeT n₁).mul (Num.ofSizeT n₂))
  | a, b => mpzToNat (a.toNum.mul b.toNum)

/--
`lean_nat_mod`, which returns the dividend when the divisor is zero:
```
static inline lean_obj_res lean_nat_mod(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t n1 = lean_unbox(a1);
        size_t n2 = lean_unbox(a2);
        if (n2 == 0)
            return lean_box(n1);
        else
            return lean_box(n1 % n2);
    } else {
        return lean_nat_big_mod(a1, a2);
    }
}
```
-/
def natMod : NatObj → NatObj → NatObj
  | .small n₁ h₁, .small n₂ _ =>
    if n₂ = 0 then .small n₁ h₁
    else .small (n₁ % n₂) (Nat.le_trans (Nat.mod_le ..) h₁)
  | .small n₁ h₁, .big _ _ => .small n₁ h₁
  | .big m₁ h₁, .small n₂ h₂ =>
    if h : n₂ = 0 then .big m₁ h₁
    else mpzToNat (m₁.mod (Num.ofSizeT n₂) (by
      rw [Num.val_ofSizeT n₂ (by simp only [maxSmallNat, base_eq] at *; omega)]; exact h))
  | .big m₁ _, .big m₂ h₂ => mpzToNat (m₁.mod m₂ (by omega))

/--
`lean_nat_land`, whose scalar path never unboxes:
```
static inline lean_obj_res lean_nat_land(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return (lean_object*)((size_t)(a1) & (size_t)(a2));
    } else {
        return lean_nat_big_land(a1, a2);
    }
}
```
It can do that because the tag bit is set in both operands, so `&` leaves it set
and the payload bits combine on their own.
-/
def natLand : NatObj → NatObj → NatObj
  | .small n₁ h₁, .small n₂ h₂ =>
    .small (unbox (box n₁ &&& box n₂)) (by
      rw [box_and n₁ n₂ h₁ h₂, unbox_box _ (Nat.le_trans (Nat.and_le_left ..) h₁)]
      exact Nat.le_trans (Nat.and_le_left ..) h₁)
  | a, b => mpzToNat (a.toNum.land b.toNum)

/--
`lean_nat_lor`, which keeps the tag for the same reason as `land`:
```
static inline lean_obj_res lean_nat_lor(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return (lean_object*)((size_t)(a1) | (size_t)(a2));
    } else {
        return lean_nat_big_lor(a1, a2);
    }
}
```
-/
def natLor : NatObj → NatObj → NatObj
  | .small n₁ h₁, .small n₂ h₂ =>
    .small (unbox (box n₁ ||| box n₂)) (by
      have hb : n₁ ||| n₂ ≤ maxSmallNat := by
        simp only [maxSmallNat] at *
        exact Nat.lt_succ_iff.mp (Nat.or_lt_two_pow (n := 63) (by omega) (by omega))
      rw [box_or n₁ n₂ h₁ h₂, unbox_box _ hb]; exact hb)
  | a, b => mpzToNat (a.toNum.lor b.toNum)

/--
`lean_nat_le`, whose scalar path compares the tagged values directly:
```
static inline LEAN_ALWAYS_INLINE bool lean_nat_le(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        // This comparison is UB according to the standard but allowed as per the
        // GCC documentation and the address sanitizer does not complain about it.
        return a1 <= a2;
    } else {
        return lean_nat_big_le(a1, a2);
    }
}
```
Boxing is monotone, so the comparison on the tagged values is the comparison on
the numbers; only the pointer comparison itself is outside the standard.
-/
def natBle : NatObj → NatObj → Bool
  | .small n₁ _, .small n₂ _ => box n₁ ≤ box n₂
  | .small _ _, .big _ _ => true
  | .big _ _, .small _ _ => false
  | .big m₁ _, .big m₂ _ => m₁.compare m₂ ≤ 0

/--
`lean_nat_eq`, whose scalar path compares the tagged values directly:
```
static inline LEAN_ALWAYS_INLINE bool lean_nat_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        // This comparison is UB according to the standard but allowed as per the
        // GCC documentation and the address sanitizer does not complain about it.
        return a1 == a2;
    } else {
        return lean_nat_big_eq(a1, a2);
    }
}
```
-/
def natBeq : NatObj → NatObj → Bool
  | .small n₁ _, .small n₂ _ => box n₁ == box n₂
  | .small _ _, .big _ _ => false
  | .big _ _, .small _ _ => false
  | .big m₁ _, .big m₂ _ => m₁.compare m₂ == 0

/--
`lean_nat_succ`:
```
static inline lean_obj_res lean_nat_succ(b_lean_obj_arg a) {
    if (LEAN_LIKELY(lean_is_scalar(a)))
        return lean_usize_to_nat(lean_unbox(a) + 1);
    else
        return lean_nat_big_succ(a);
}
```
-/
def natSucc : NatObj → NatObj
  | .small n h => usizeToNat (n + 1) (by simp only [maxSmallNat, base_eq] at *; omega)
  | .big m h => mpzToNatCore (m.add Num.one) (by rw [Num.val_add, Num.val_one]; omega)

/--
`lean_nat_shiftr`, and `lean_nat_big_shiftr` behind it:
```
static inline lean_obj_res lean_nat_shiftr(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t s1 = lean_unbox(a1);
        size_t s2 = lean_unbox(a2);
        size_t r = (s2 < sizeof(size_t)*8) ? s1 >> s2 : 0;
        return lean_box(r);
    } else {
        return lean_nat_big_shiftr(a1, a2);
    }
}
```
```
extern "C" LEAN_EXPORT lean_obj_res lean_nat_big_shiftr(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (!lean_is_scalar(a2)) {
        return lean_box(0); // This large of an exponent must be 0.
    }
    auto a = lean_is_scalar(a1)
           ? mpz::of_size_t(lean_unbox(a1))
           : mpz_value(a1);
    size_t s = lean_unbox(a2);
    // If the shift amount is large, then we fail if it is not large
    // enough to zero out all the bits.
    if (s > UINT_MAX) {
        if (a.log2() >= s) {
            lean_internal_panic("Nat.shiftr exponent is too big");
        } else {
            return lean_box(0);
        }
    }
    mpz r;
    div2k(r, a, s);
    return mpz_to_nat(r);
}
```
NOTE: the scalar path's `s2 < 64` test is not there for the answer's sake - a
scalar shifted by 64 or more is zero either way - but because `>>` by the
operand width or more is undefined in C++, the same hazard `div_normalize` runs
into.

NOTE: `a.log2() >= s` is `2 ^ s ≤ a` for a nonzero `a`, which a `big` object
always is, so that is how the panic's guard is written here.
-/
def natShiftRight (a b : NatObj) : NatObj :=
  match a, b with
  | .small n₁ h₁, .small n₂ _ =>
    .small (if n₂ < 64 then n₁ >>> n₂ else 0) (by
      split
      · exact Nat.le_trans (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self ..) h₁
      · exact Nat.zero_le _)
  | _, .big _ _ => .small 0 (Nat.zero_le _)
  | .big m₁ _, .small n₂ _ =>
    if base ≤ n₂ then
      if 2 ^ n₂ ≤ m₁.val then panic! "Nat.shiftr exponent is too big"
      else .small 0 (Nat.zero_le _)
    else mpzToNat (m₁.shiftRight n₂)

/--
`lean_nat_shiftl`:
```
extern "C" LEAN_EXPORT lean_obj_res lean_nat_shiftl(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    // Special case for shifted value is 0.
    if (lean_is_scalar(a1) && lean_unbox(a1) == 0) {
        return lean_box(0);
    }
    auto a = lean_is_scalar(a1)
           ? mpz::of_size_t(lean_unbox(a1))
           : mpz_value(a1);
    if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
        lean_internal_panic("Nat.shiftl exponent is too big");
    }
    mpz r;
    mul2k(r, a, lean_unbox(a2));
    return mpz_to_nat(r);
}
```
The panic is the precondition `hb`: an exponent past `UINT_MAX` has no answer to
give. A `big` object is never zero, so testing the scalar for zero is testing
the value.
-/
def natShiftLeft (a b : NatObj) : NatObj :=
  if a.val = 0 then .small 0 (Nat.zero_le _)
  else if base ≤ b.val then panic! "Nat.shiftl exponent is too big"
  else mpzToNat (a.toNum.shiftLeft b.val)

/--
`lean_nat_lxor`:
```
static inline lean_obj_res lean_nat_lxor(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return lean_box(lean_unbox(a1) ^ lean_unbox(a2));
    } else {
        return lean_nat_big_xor(a1, a2);
    }
}
```
Unlike `land` and `lor` this unboxes first, because `^` on two tagged values
would clear the tag rather than keep it.
-/
def natXor : NatObj → NatObj → NatObj
  | .small n₁ h₁, .small n₂ h₂ =>
    .small (n₁ ^^^ n₂) (by
      simp only [maxSmallNat] at *
      exact Nat.lt_succ_iff.mp (Nat.xor_lt_two_pow (n := 63) (by omega) (by omega)))
  | a, b => mpzToNat (a.toNum.xor b.toNum)

/--
`lean_nat_gcd`:
```
extern "C" LEAN_EXPORT lean_obj_res lean_nat_gcd(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (lean_is_scalar(a1)) {
      if (lean_is_scalar(a2))
        return mpz_to_nat(gcd(mpz::of_size_t(lean_unbox(a1)), mpz::of_size_t(lean_unbox(a2))));
      else
        return mpz_to_nat(gcd(mpz::of_size_t(lean_unbox(a1)), mpz_value(a2)));
    } else {
      if (lean_is_scalar(a2))
        return mpz_to_nat(gcd(mpz_value(a1), mpz::of_size_t(lean_unbox(a2))));
      else
        return mpz_to_nat(gcd(mpz_value(a1), mpz_value(a2)));
    }
}
```
All four arms are `gcd` on the two values as `mpz`, which is what `toNum` reads
off an object, so the dispatch collapses here.
-/
def natGcd (a b : NatObj) : NatObj := mpzToNat (a.toNum.gcd b.toNum)

/--
`lean_nat_pow`:
```
extern "C" LEAN_EXPORT lean_obj_res lean_nat_pow(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
        lean_internal_panic("Nat.pow exponent is too big");
    }
    if (lean_is_scalar(a1))
        return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)).pow(lean_unbox(a2)));
    else
        return mpz_to_nat(mpz_value(a1).pow(lean_unbox(a2)));
}
```
The exponent is an object here rather than an `unsigned`, and the guard is what
bounds `type_checker::reduce_pow` to `UINT_MAX`. A `big` object exceeds
`UINT_MAX` on its own, so `!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX` is
the single test `base ≤ p.val`.
-/
def natPow (a p : NatObj) : NatObj :=
  if base ≤ p.val then panic! "Nat.pow exponent is too big"
  else
    match a with
    | .small n _ => mpzToNat ((Num.ofSizeT n).pow (UInt32.ofNat p.val))
    | .big m _ => mpzToNat (m.pow (UInt32.ofNat p.val))


end ObjectModel

section ObjectProofs


/-!
## Proofs for the `lean_object` layer
-/

/--
`lean_nat_le`'s fast path compares the boxed values directly:
```
        // This comparison is UB according to the standard but allowed as per the
        // GCC documentation and the address sanitizer does not complain about it.
        return a1 < a2;
```
Boxing is monotone, so the comparison on the tagged values is the comparison on
the numbers. Only the pointer comparison itself is outside the standard.
-/
theorem box_le_box (m n : Nat) (hm : m ≤ maxSmallNat) (hn : n ≤ maxSmallNat) :
    (box m ≤ box n) ↔ m ≤ n := by
  rw [UInt64.le_iff_toNat_le, toNat_box m hm, toNat_box n hn]
  omega

@[simp] theorem mpzToNat_val (m : Num) : (mpzToNat m).val = m.val := by
  unfold mpzToNat; split <;> rfl

@[simp] theorem mpzToNatCore_val (m : Num) (h : maxSmallNat < m.val) :
    (mpzToNatCore m h).val = m.val := rfl

/--
`lean_nat_div` divides, for every pair of objects. There is no precondition:
division by zero is a branch rather than an assumption, and the branch that
returns zero without dividing is sound because a `big` object never holds a
value a scalar could have held, which is what the type records and what the
`lean_assert` in `lean_nat_big_div` only checks in a debug build.
-/
theorem natDiv_val (a b : NatObj) : (natDiv a b).val = a.val / b.val := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      simp only [natDiv]
      split <;> rename_i h
      · subst h; simp [NatObj.val]
      · rfl
    | big m₂ h₂ =>
      simp only [NatObj.val]
      exact (Nat.div_eq_of_lt (by omega)).symm
  | big m₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      simp only [natDiv]
      split <;> rename_i h
      · subst h; simp [NatObj.val]
      · rw [mpzToNat_val, Num.val_div, NatObj.val, NatObj.val,
          Num.val_ofSizeT n₂ (by simp only [maxSmallNat, base_eq] at *; omega)]
    | big m₂ h₂ =>
      simp only [natDiv]
      rw [mpzToNat_val, Num.val_div, NatObj.val, NatObj.val]

private theorem small_lt_base_sq {n : Nat} (h : n ≤ maxSmallNat) : n < base ^ 2 := by
  simp only [maxSmallNat, base_eq] at *; omega

@[simp] theorem NatObj.val_toNum (a : NatObj) : a.toNum.val = a.val := by
  cases a with
  | small n h => rw [toNum, NatObj.val, Num.val_ofSizeT n (small_lt_base_sq h)]
  | big m _ => rfl

@[simp] theorem usizeToNat_val (n : Nat) (h64 : n < base ^ 2) : (usizeToNat n h64).val = n := by
  unfold usizeToNat; split
  · rfl
  · rw [NatObj.val, Num.val_ofSizeT n h64]

@[simp] theorem natAdd_val (a b : NatObj) : (natAdd a b).val = a.val + b.val := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ => simp only [natAdd]; rw [usizeToNat_val]; rfl
    | big m₂ _ =>
      simp only [natAdd]
      rw [mpzToNatCore_val, Num.val_add, Num.val_ofSizeT n₁ (small_lt_base_sq h₁)]; rfl
  | big m₁ _ =>
    cases b with
    | small n₂ h₂ =>
      simp only [natAdd]
      rw [mpzToNatCore_val, Num.val_add, Num.val_ofSizeT n₂ (small_lt_base_sq h₂)]; rfl
    | big m₂ _ => simp only [natAdd]; rw [mpzToNatCore_val, Num.val_add]; rfl

@[simp] theorem natSub_val (a b : NatObj) : (natSub a b).val = a.val - b.val := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      simp only [natSub]
      split <;> rename_i h
      · show (0 : Nat) = n₁ - n₂; omega
      · rfl
    | big m₂ h₂ => show (0 : Nat) = n₁ - m₂.val; omega
  | big m₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      simp only [natSub]
      rw [mpzToNat_val, Num.val_sub, Num.val_ofSizeT n₂ (small_lt_base_sq h₂)]; rfl
    | big m₂ _ =>
      simp only [natSub]
      split <;> rename_i h
      · show (0 : Nat) = m₁.val - m₂.val; omega
      · rw [mpzToNat_val, Num.val_sub]; rfl

@[simp] theorem natMul_val (a b : NatObj) : (natMul a b).val = a.val * b.val := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      simp only [natMul]
      split <;> rename_i h
      · subst h; simp [NatObj.val]
      · split
        · rfl
        · rw [mpzToNat_val, Num.val_mul, Num.val_ofSizeT n₁ (small_lt_base_sq h₁),
            Num.val_ofSizeT n₂ (small_lt_base_sq h₂)]
          rfl
    | big m₂ _ => simp only [natMul]; rw [mpzToNat_val, Num.val_mul, NatObj.val_toNum,
        NatObj.val_toNum]
  | big m₁ _ =>
    cases b <;> (simp only [natMul]
                 rw [mpzToNat_val, Num.val_mul, NatObj.val_toNum, NatObj.val_toNum])

@[simp] theorem natMod_val (a b : NatObj) : (natMod a b).val = a.val % b.val := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      simp only [natMod]
      split <;> rename_i h
      · subst h; simp [NatObj.val]
      · rfl
    | big m₂ h₂ =>
      show n₁ = n₁ % m₂.val
      exact (Nat.mod_eq_of_lt (by omega)).symm
  | big m₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      simp only [natMod]
      split <;> rename_i h
      · subst h; show m₁.val = m₁.val % 0; simp
      · rw [mpzToNat_val, Num.val_mod, Num.val_ofSizeT n₂ (small_lt_base_sq h₂)]; rfl
    | big m₂ _ => simp only [natMod]; rw [mpzToNat_val, Num.val_mod]; rfl

@[simp] theorem natLand_val (a b : NatObj) : (natLand a b).val = a.val &&& b.val := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      show unbox (box n₁ &&& box n₂) = _
      rw [box_and n₁ n₂ h₁ h₂, unbox_box _ (Nat.le_trans (Nat.and_le_left ..) h₁)]
      rfl
    | big m₂ _ => simp only [natLand]; rw [mpzToNat_val, Num.val_land, NatObj.val_toNum,
        NatObj.val_toNum]
  | big m₁ _ =>
    cases b <;> (simp only [natLand]
                 rw [mpzToNat_val, Num.val_land, NatObj.val_toNum, NatObj.val_toNum])

@[simp] theorem natLor_val (a b : NatObj) : (natLor a b).val = a.val ||| b.val := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      have hb : n₁ ||| n₂ ≤ maxSmallNat := by
        simp only [maxSmallNat] at *
        exact Nat.lt_succ_iff.mp (Nat.or_lt_two_pow (n := 63) (by omega) (by omega))
      show unbox (box n₁ ||| box n₂) = _
      rw [box_or n₁ n₂ h₁ h₂, unbox_box _ hb]
      rfl
    | big m₂ _ => simp only [natLor]; rw [mpzToNat_val, Num.val_lor, NatObj.val_toNum,
        NatObj.val_toNum]
  | big m₁ _ =>
    cases b <;> (simp only [natLor]
                 rw [mpzToNat_val, Num.val_lor, NatObj.val_toNum, NatObj.val_toNum])

@[simp] theorem natBle_val (a b : NatObj) : natBle a b = decide (a.val ≤ b.val) := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      show decide (box n₁ ≤ box n₂) = decide (n₁ ≤ n₂)
      simp only [decide_eq_decide]
      exact box_le_box n₁ n₂ h₁ h₂
    | big m₂ h₂ => exact (decide_eq_true (by omega : n₁ ≤ m₂.val)).symm
  | big m₁ h₁ =>
    cases b with
    | small n₂ h₂ => exact (decide_eq_false (by omega : ¬ (m₁.val ≤ n₂))).symm
    | big m₂ _ =>
      show decide (m₁.compare m₂ ≤ (0 : Int)) = decide (m₁.val ≤ m₂.val)
      simp only [decide_eq_decide]
      exact compare_le_zero m₁ m₂

/-- Boxing is injective, which is what makes the pointer comparison meaningful. -/
theorem box_inj (m n : Nat) (hm : m ≤ maxSmallNat) (hn : n ≤ maxSmallNat) :
    box m = box n ↔ m = n := by
  constructor
  · intro h; rw [← unbox_box m hm, ← unbox_box n hn, h]
  · grind

@[simp] theorem natBeq_val (a b : NatObj) : natBeq a b = decide (a.val = b.val) := by
  have hcmp : ∀ x y : Num, (x.compare y == 0) = decide (x.val = y.val) := by
    intro x y
    rw [Num.compare_spec]
    split <;> rename_i h1
    · grind
    · grind
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      show (box n₁ == box n₂) = decide (n₁ = n₂)
      by_cases h : n₁ = n₂
      · grind
      · have hne : box n₁ ≠ box n₂ := fun hb => h ((box_inj n₁ n₂ h₁ h₂).mp hb)
        simp [hne, h]
    | big m₂ h₂ => exact (decide_eq_false (by omega : ¬ (n₁ = m₂.val))).symm
  | big m₁ h₁ =>
    cases b with
    | small n₂ h₂ => exact (decide_eq_false (by omega : ¬ (m₁.val = n₂))).symm
    | big m₂ _ => show (m₁.compare m₂ == 0) = decide (m₁.val = m₂.val); exact hcmp m₁ m₂

@[simp] theorem natSucc_val (a : NatObj) : (natSucc a).val = a.val + 1 := by
  cases a with
  | small n h => simp only [natSucc]; rw [usizeToNat_val]; rfl
  | big m _ => simp only [natSucc]; rw [mpzToNatCore_val, Num.val_add]; rfl

@[simp] theorem natShiftRight_val (a b : NatObj) (hb : base ≤ b.val → a.val < 2 ^ b.val) :
    (natShiftRight a b).val = a.val >>> b.val := by
  have hzero : ∀ x y : Nat, x < 2 ^ y → (0 : Nat) = x >>> y := by
    intro x y h; rw [Nat.shiftRight_eq_div_pow]; exact (Nat.div_eq_of_lt h).symm
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      show (if n₂ < 64 then n₁ >>> n₂ else 0) = n₁ >>> n₂
      split <;> rename_i h
      · rfl
      · refine hzero n₁ n₂ ?_
        have hp : (2:Nat) ^ 64 ≤ 2 ^ n₂ := Nat.pow_le_pow_right (by omega) (by omega)
        simp only [maxSmallNat] at h₁
        omega
    | big m₂ h₂ =>
      refine hzero n₁ m₂.val (hb ?_)
      show base ≤ m₂.val
      simp only [maxSmallNat] at h₂
      simp only [base_eq]
      omega
  | big m₁ h₁ =>
    cases b with
    | small n₂ h₂ =>
      show (if base ≤ n₂ then (if 2 ^ n₂ ≤ m₁.val then _ else _) else mpzToNat _).val
        = m₁.val >>> n₂
      split <;> rename_i h
      · have hlt : m₁.val < 2 ^ n₂ := hb (by show base ≤ n₂; omega)
        simp only [show ¬(2 ^ n₂ ≤ m₁.val) from by omega]
        exact hzero m₁.val n₂ hlt
      · rw [mpzToNat_val, Num.val_shiftRight, Nat.shiftRight_eq_div_pow]
    | big m₂ h₂ =>
      refine hzero m₁.val m₂.val (hb ?_)
      show base ≤ m₂.val
      simp only [maxSmallNat] at h₂
      simp only [base_eq]
      omega

@[simp] theorem natShiftLeft_val (a b : NatObj) (hb : b.val < base) :
    (natShiftLeft a b).val = a.val <<< b.val := by
  rw [natShiftLeft]
  split <;> rename_i h
  · show (0 : Nat) = _
    rw [h, Nat.shiftLeft_eq, Nat.zero_mul]
  · split <;> rename_i h2
    · exact absurd h2 (by omega)
    · rw [mpzToNat_val, Num.val_shiftLeft, NatObj.val_toNum, Nat.shiftLeft_eq]

@[simp] theorem natXor_val (a b : NatObj) : (natXor a b).val = a.val ^^^ b.val := by
  cases a with
  | small n₁ h₁ =>
    cases b with
    | small n₂ h₂ => rfl
    | big m₂ _ => simp only [natXor]; rw [mpzToNat_val, Num.val_xor, NatObj.val_toNum,
        NatObj.val_toNum]
  | big m₁ _ =>
    cases b <;> (simp only [natXor]
                 rw [mpzToNat_val, Num.val_xor, NatObj.val_toNum, NatObj.val_toNum])

@[simp] theorem natGcd_val (a b : NatObj) : (natGcd a b).val = Nat.gcd a.val b.val := by
  rw [natGcd, mpzToNat_val, Num.val_gcd, NatObj.val_toNum, NatObj.val_toNum]

@[simp] theorem natPow_val (a p : NatObj) (hp : p.val < base) :
    (natPow a p).val = a.val ^ p.val := by
  unfold natPow
  split <;> rename_i h
  · exact absurd h (by omega)
  · cases a with
    | small n hn =>
      rw [mpzToNat_val, Num.val_pow, UInt32.toNat_ofNat_of_lt' hp,
        Num.val_ofSizeT n (small_lt_base_sq hn)]
      rfl
    | big m _ =>
      rw [mpzToNat_val, Num.val_pow, UInt32.toNat_ofNat_of_lt' hp]
      rfl

end ObjectProofs

end Mpn
