/-!
# Lean transliteration of the runtime's GMP-free bignum core

`src/runtime/mpn.cpp` implements multi-precision naturals as little-endian
arrays of `uint32_t` digits. It is the arithmetic Lean uses when built with
`USE_GMP=OFF` (the 32-bit and WebAssembly targets); both of those CI
configurations are currently disabled, so the code has no automated coverage.

This file transliterates it statement by statement so that the algorithms can
be checked against `Nat`, which is what `#eval mpnCheck` at the bottom does, and
so that they can be proved correct, which `denote_add`, `denote_sub` and
`denote_mul` do for `mpn_add`, `mpn_sub` and `mpn_mul`. Deviations from the C++
are marked `NOTE:`.

A transliteration is only worth as much as its fidelity to the original, so
`Mpn.Test.emit` prints the model's results in the format that
`mpn_model_crosscheck.cpp` prints the real `mpn.cpp`'s in, on the same
pseudorandom operands; the two agree byte for byte.
-/

namespace Mpn

abbrev Digit := UInt32
abbrev DoubleDigit := UInt64

def digitBits : Nat := 32
def base : Nat := 4294967296
def maskFirst : Digit := 0x80000000

private def lo (t : DoubleDigit) : Digit := t.toUInt32
private def hi (t : DoubleDigit) : Digit := (t >>> 32).toUInt32

/-! ## Denotation -/

/-- The first `j` digits of `a`, little-endian, read as a natural. -/
def denoteN (a : Array Digit) : Nat → Nat
  | 0 => 0
  | j+1 => denoteN a j + (a.getD j 0).toNat * base ^ j

/-- `a` read as a little-endian base-`2^32` natural. -/
def denote (a : Array Digit) : Nat := denoteN a a.size

theorem getD_lt (a : Array Digit) (j : Nat) : (a.getD j 0).toNat < base := by
  simp only [Array.getD]
  split <;> exact UInt32.toNat_lt_size ..

theorem getD_of_ge (a : Array Digit) {j : Nat} (h : a.size ≤ j) : a.getD j 0 = 0 := by
  simp [Nat.not_lt_of_ge h]

theorem getD_push_lt (c : Array Digit) (d : Digit) {j : Nat} (h : j < c.size) :
    (c.push d).getD j 0 = c.getD j 0 := by
  simp [Array.getElem?_push, Nat.ne_of_lt h, h]

theorem getD_push_eq (c : Array Digit) (d : Digit) : (c.push d).getD c.size 0 = d := by simp

theorem getD_pop_lt (c : Array Digit) {j : Nat} (h : j < c.pop.size) :
    c.pop.getD j 0 = c.getD j 0 := by
  simp only [Array.size_pop] at h
  have hj : j < c.size := by omega
  simp [h, hj]

theorem denoteN_lt (a : Array Digit) (j : Nat) : denoteN a j < base ^ j := by
  induction j with
  | zero => simp [denoteN, base]
  | succ j ih =>
    have hd := getD_lt a j
    have key : base ^ j + (base - 1) * base ^ j = base ^ (j+1) := by
      rw [Nat.pow_succ]; generalize base ^ j = p; unfold base; omega
    simp only [denoteN]
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
    · rw [denoteN, getD_of_ge a h', ih h']; simp

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
  have hlast : c.getD c.pop.size 0 = 0 := by rw [hsz]; exact hz
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
  | zero => have : n = 0 := by omega
            subst this; rfl
  | succ m ih =>
    rcases Nat.lt_or_ge m n with h' | h'
    · have : n = m + 1 := by omega
      subst this; rfl
    · rw [denoteN, h m h', ih h']; simp

theorem denote_of_high_zero (c : Array Digit) {n : Nat} (hn : n ≤ c.size)
    (h : ∀ idx, n ≤ idx → c.getD idx 0 = 0) : denote c = denoteN c n :=
  denoteN_of_high_zero c hn h

/-! ## `mpn_compare` -/

/--
`mpn_compare`. The C++ latches `res` and runs the loop to completion; returning
early is observationally the same.
-/
def compare (a b : Array Digit) : Int := Id.run do
  let len := max a.size b.size
  for k in [0:len] do
    let j := len - 1 - k
    let u_j := a.getD j 0
    let v_j := b.getD j 0
    if u_j > v_j then return 1
    if u_j < v_j then return -1
  return 0

/-! ## `mpn_add` -/

/-- One iteration of `mpn_add`'s loop body. -/
def addStep (a b : Array Digit) (s : Array Digit × Digit) (j : Nat) : Array Digit × Digit :=
  let (c, k) := s
  let u_j := a.getD j 0
  let v_j := b.getD j 0
  let r := u_j + v_j
  let c1 := r < u_j
  let cj := r + k
  let c2 := cj < r
  (c.push cj, if c1 || c2 then 1 else 0)

/-- `mpn_add`'s digit loop: `len` result digits plus the final carry. -/
def addLoop (a b : Array Digit) (len : Nat) : Array Digit × Digit :=
  (List.range len).foldl (addStep a b) (#[], 0)

/-- `for (os = len+1; os > 1 && c[os-1] == 0; ) os--;` -/
def trim (c : Array Digit) : Array Digit :=
  if 1 < c.size && c.getD (c.size - 1) 0 == 0 then trim c.pop else c
termination_by c.size
decreasing_by simp_all; omega

/--
`mpn_add`. The C++ writes `len+1` digits into a caller-supplied buffer and
returns the trimmed length in `*plngc`; here the trimmed prefix is the result.
-/
def add (a b : Array Digit) : Array Digit :=
  let len := max a.size b.size
  let (c, k) := addLoop a b len
  trim (c.push k)

/-! ## `mpn_sub` -/

def subStep (a b : Array Digit) (s : Array Digit × Digit) (j : Nat) : Array Digit × Digit :=
  let (c, k) := s
  let u_j := a.getD j 0
  let v_j := b.getD j 0
  let r := u_j - v_j
  let c1 := r > u_j
  let cj := r - k
  let c2 := cj > r
  (c.push cj, if c1 || c2 then 1 else 0)

/-- `mpn_sub`'s digit loop: `len` result digits plus the final borrow. -/
def subLoop (a b : Array Digit) (len : Nat) : Array Digit × Digit :=
  (List.range len).foldl (subStep a b) (#[], 0)

/-- `mpn_sub`. Returns the `max lnga lngb` result digits and the final borrow. -/
def sub (a b : Array Digit) : Array Digit × Digit :=
  subLoop a b (max a.size b.size)

/-! ## `mpn_mul` -/

/-- One iteration of `mpn_mul`'s inner loop: `c[i+j] := a[i] * v_j + c[i+j] + k`. -/
def mulInnerStep (a : Array Digit) (v_j : Digit) (j : Nat)
    (s : Array Digit × Digit) (i : Nat) : Array Digit × Digit :=
  let (c, k) := s
  let u_i := a.getD i 0
  let t : DoubleDigit :=
    u_i.toUInt64 * v_j.toUInt64 + (c.getD (i + j) 0).toUInt64 + k.toUInt64
  (c.set! (i + j) (lo t), hi t)

/-- `mpn_mul`'s inner loop over `lnga` digits of `a`, leaving a carry. -/
def mulInner (a : Array Digit) (v_j : Digit) (j : Nat) (c : Array Digit) (lnga : Nat) :
    Array Digit × Digit :=
  (List.range lnga).foldl (mulInnerStep a v_j j) (c, 0)

/--
One iteration of `mpn_mul`'s outer loop. The `v_j == 0` branch is Knuth's
optional shortcut: with a zero multiplier the inner loop would leave `c`
untouched and its carry at zero anyway.
-/
def mulOuterStep (a b : Array Digit) (c : Array Digit) (j : Nat) : Array Digit :=
  let v_j := b.getD j 0
  if v_j == 0 then
    c.set! (j + a.size) 0
  else
    let (c, k) := mulInner a v_j j c a.size
    c.set! (j + a.size) k

/--
`mpn_mul`'s outer loop over the first `m` digits of `b`.

NOTE: the C++ zeroes only `c[0..lnga)` and relies on the outer loop to write
every digit from `lnga` up; zeroing the whole buffer here computes the same
result and states the invariant more simply.
-/
def mulLoop (a b : Array Digit) (m : Nat) : Array Digit :=
  (List.range m).foldl (mulOuterStep a b) (Array.replicate (a.size + b.size) 0)

/-- `mpn_mul`. Returns `lnga + lngb` digits. -/
def mul (a b : Array Digit) : Array Digit := mulLoop a b b.size

/-! ## division -/

/-- `for i in [0:n] do if p i then d := d + 1 else break` -/
private def countWhile (p : Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, i => if p i then 1 + countWhile p fuel (i+1) else 0

/--
The leading-zero count of `x`, as `div_normalize`'s `while` loop computes it.

NOTE: the C++ `while (lden > 0 && ((denom[lden-1] << d) & MASK_FIRST) == 0) d++;`
shifts by `d == 32` once the top denominator digit is zero, which is undefined
behaviour. The bounded count below stops at 32 instead. Callers reach `mpn_div`
only through `mpz`, whose sizes are normalized, so the top digit is nonzero
unless the denominator is zero, which `lean_nat_div` rejects first.
-/
def leadingZeros (x : Digit) : Nat :=
  countWhile (fun i => (x <<< (UInt32.ofNat i)) &&& maskFirst == 0) digitBits 0

/--
`len` digits of `a` shifted left by `d` bits: digit `i` is
`(a[i] << d) | (a[i-1] >> (32-d))`. The `d == 0` case is separate because the
C++ needs it to be: shifting a digit by 32 is undefined there.

Each output digit reads only the input, so this is the two `div_normalize`
loops written as the map they are.
-/
def shiftLeftDigits (a : Array Digit) (d len : Nat) : Array Digit :=
  (Array.range len).map fun i =>
    if d == 0 then a.getD i 0
    else (a.getD i 0 <<< UInt32.ofNat d) |||
      (if i == 0 then 0 else a.getD (i-1) 0 >>> UInt32.ofNat (digitBits - d))

/--
`div_normalize`. Returns the shift `d` together with the normalized numerator
(`lnum+1` digits) and denominator (`lden` digits).

The C++ branches three ways, but its `d == 0` copy is exactly `shiftLeftDigits`
at `d = 0`, so only the degenerate case needs its own branch.

NOTE: with a nonzero shift and an empty numerator the C++ leaves both buffers
zeroed and reports `d = 0`. No caller reaches it: `mpn_div` and `mpn_to_string`
both pass `lnum ≥ 1`.
-/
def divNormalize (numer denom : Array Digit) : Nat × Array Digit × Array Digit :=
  let lnum := numer.size
  let lden := denom.size
  let d := if lden = 0 then 0 else leadingZeros (denom.getD (lden - 1) 0)
  if lnum = 0 && d ≠ 0 then
    (0, Array.replicate (lnum + 1) 0, Array.replicate lden 0)
  else
    (d, shiftLeftDigits numer d (lnum + 1), shiftLeftDigits denom d lden)

/-- The low `d` bits of a digit, as `div_unnormalize`'s `LAST_BITS` computes them. -/
def lastBits (x : Digit) (d : Nat) : Digit :=
  (x <<< (UInt32.ofNat (digitBits - d))) >>> (UInt32.ofNat (digitBits - d))

/--
`len` digits of `a` shifted right by `d` bits: digit `i` is
`(a[i] >> d) | (lastBits a[i+1] << (32-d))`. The top digit takes nothing from
above, as the C++ does, and `d == 0` is separate for the same reason as in
`shiftLeftDigits`.
-/
def shiftRightDigits (a : Array Digit) (d len : Nat) : Array Digit :=
  (Array.range len).map fun i =>
    if d == 0 then a.getD i 0
    else (a.getD i 0 >>> UInt32.ofNat d) |||
      (if i + 1 == len then 0
       else lastBits (a.getD (i+1) 0) d <<< UInt32.ofNat (digitBits - d))

/-- `div_unnormalize`. Produces `lden` remainder digits. -/
def divUnnormalize (numer : Array Digit) (lden d : Nat) : Array Digit :=
  shiftRightDigits numer d lden

/--
`div_1`. Single-digit division; returns the updated numerator (holding the
remainder) and `numer.size - 1` quotient digits.
-/
def div1 (numer : Array Digit) (denom : Digit) : Array Digit × Array Digit := Id.run do
  let n := numer.size
  let mut u := numer
  let mut quot : Array Digit := Array.replicate (n - 1) 0
  for k in [0:n-1] do
    let j := n - 1 - k
    let temp : DoubleDigit := (u[j]!.toUInt64 <<< 32) ||| u[j-1]!.toUInt64
    let q_hat := temp / denom.toUInt64
    let ms := temp - q_hat * denom.toUInt64
    let borrow := ms > temp
    u := u.set! (j-1) (lo ms)
    u := u.set! j (hi ms)
    quot := quot.set! (j-1) (lo q_hat)
    if borrow then
      quot := quot.set! (j-1) (quot[j-1]! - 1)
      u := u.set! j (u[j-1]! + denom)
  return (u, quot)

/--
The `recheck:` correction loop of `div_n`. Knuth bounds it at two iterations;
fuel exhaustion is reported so `mpnCheck` can notice if that is ever wrong.
-/
private def recheck (dn1 dn2 : Digit) (nu : Digit) :
    Nat → DoubleDigit → DoubleDigit → DoubleDigit × DoubleDigit × Bool
  | 0, q_hat, r_hat => (q_hat, r_hat, true)
  | fuel+1, q_hat, r_hat =>
    if q_hat >>> 32 != 0 || q_hat * dn2.toUInt64 > ((r_hat <<< 32) + nu.toUInt64) then
      let q_hat := q_hat - 1
      let r_hat := r_hat + dn1.toUInt64
      if r_hat >>> 32 == 0 then recheck dn1 dn2 nu fuel q_hat r_hat
      else (q_hat, r_hat, false)
    else (q_hat, r_hat, false)

/--
`div_n`, i.e. Knuth's Algorithm D. Returns the updated numerator (holding the
normalized remainder), `m` quotient digits, and whether the correction loop ran
out of fuel.
-/
def divN (numer denom : Array Digit) : Array Digit × Array Digit × Bool := Id.run do
  let n := denom.size
  let m := numer.size - n
  let mut u := numer
  let mut quot : Array Digit := Array.replicate m 0
  let mut stuck := false
  for k in [0:m] do
    let j := m - 1 - k
    let temp : DoubleDigit := (u[j+n]!.toUInt64 <<< 32) ||| u[j+n-1]!.toUInt64
    let q_hat := temp / denom[n-1]!.toUInt64
    let r_hat := temp % denom[n-1]!.toUInt64
    let (q_hat, _, s) := recheck denom[n-1]! denom[n-2]! (u.getD (j+n-2) 0) 8 q_hat r_hat
    stuck := stuck || s
    let q_hat_small := lo q_hat
    let ms := mul #[q_hat_small] denom
    let (diff, borrow) := sub (u.extract j (j+n+1)) ms
    for i in [0:n+1] do u := u.set! (j+i) diff[i]!
    quot := quot.set! j q_hat_small
    if borrow != 0 then
      quot := quot.set! j (quot[j]! - 1)
      let ab := add denom (u.extract j (j+n+1))
      for i in [0:n+1] do u := u.set! (j+i) (ab.getD i 0)
  return (u, quot, stuck)

/--
`mpn_div`. Returns `lnum - lden + 1` quotient digits, `lden` remainder digits,
and whether `div_n`'s correction loop ran out of fuel.

NOTE: the `lnum < lden` branch of the C++ computes its loop bound
`lnum - lden + 1` in `size_t`, which underflows to `SIZE_MAX` whenever
`lden > lnum + 1` and then overruns the quotient buffer. Every in-tree caller
checks `lden <= lnum` first, so the branch is dead; the model returns an empty
quotient there.
-/
def div (numer denom : Array Digit) : Array Digit × Array Digit × Bool := Id.run do
  let lnum := numer.size
  let lden := denom.size
  if lnum < lden then
    let quot : Array Digit := Array.replicate (lnum + 1 - lden) 0
    let rem : Array Digit := (Array.range lden).map fun i => numer.getD i 0
    return (quot, rem, false)
  if lnum == 1 && lden == 1 then
    return (#[numer[0]! / denom[0]!], #[numer[0]! % denom[0]!], false)
  else if lnum == lden && numer[lnum-1]! < denom[lden-1]! then
    let quot : Array Digit := Array.replicate (lnum - lden + 1) 0
    let rem : Array Digit := (Array.range lden).map fun i => numer.getD i 0
    return (quot, rem, false)
  else
    let (d, u, v) := divNormalize numer denom
    let mut stuck := false
    let mut u := u
    let mut quot : Array Digit := Array.replicate (lnum - lden + 1) 0
    if lden == 1 then
      let (u', q) := div1 u v[0]!
      u := u'
      for i in [0:min q.size quot.size] do quot := quot.set! i q[i]!
    else
      let (u', q, s) := divN u v
      u := u'
      stuck := s
      for i in [0:min q.size quot.size] do quot := quot.set! i q[i]!
    let rem := divUnnormalize u lden d
    return (quot, rem, stuck)

/-! ## `mpn_to_string` -/

/--
`mpn_to_string`.

NOTE: for `lng == 0` the C++ decrements `j` from `0` past the end of `size_t`
and then swaps around `SIZE_MAX/2` character pairs. `mpz::m_size` is always at
least one, so no caller can reach it.
-/
def toString (a : Array Digit) : String := Id.run do
  let lng := a.size
  if lng == 1 then
    return ToString.toString a[0]!.toNat
  let mut temp := a
  let mut digits : Array Char := #[]
  let ten : Array Digit := #[10]
  -- `while (!temp.empty() && (temp.size() > 1 || temp[0] != 0))`
  for _ in [0:32 * lng + 16] do
    if temp.isEmpty || (temp.size == 1 && temp[0]! == 0) then break
    let (d, t_numer, t_denom) := divNormalize temp ten
    let (u, q) := div1 t_numer t_denom[0]!
    let rem := divUnnormalize u 1 d
    temp := q.extract 0 temp.size
    digits := digits.push (Char.ofNat (48 + rem[0]!.toNat))
    for _ in [0:lng] do
      if !temp.isEmpty && temp.back! == 0 then temp := temp.pop else break
  return String.ofList digits.toList.reverse

/-! ## Correctness of `mpn_add` -/

/-- The digit-level carry identity: `c[j] + carry * 2^32 = u_j + v_j + k`. -/
theorem addStep_digit (u v k : Digit) (hk : k.toNat ≤ 1) :
    ((u + v) + k).toNat
        + (if (u + v) < u || ((u + v) + k) < (u + v) then (1 : Digit) else 0).toNat * base
      = u.toNat + v.toNat + k.toNat := by
  have hsz : (UInt32.size : Nat) = 4294967296 := rfl
  have hu := UInt32.toNat_lt_size u
  have hv := UInt32.toNat_lt_size v
  simp only [base]
  simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_add, hsz] at *
  split <;> rename_i h <;>
    simp only [Bool.or_eq_true, decide_eq_true_eq, UInt32.toNat_ofNat] at * <;> omega

theorem addStep_carry_le (a b : Array Digit) (s : Array Digit × Digit) (j : Nat) :
    (addStep a b s j).2.toNat ≤ 1 := by
  simp only [addStep]; split <;> simp

private theorem add_combine {dc k p ua ub cj carry dna dnb B : Nat}
    (hval : dc + k * p = dna + dnb)
    (hstep : cj + carry * B = ua + ub + k) :
    dc + cj * p + carry * (p * B) = (dna + ua * p) + (dnb + ub * p) := by
  grind

/--
The loop invariant of `mpn_add`: after `len` iterations the digits written so
far plus the outstanding carry denote the sum of the first `len` digits of the
two inputs.
-/
theorem addLoop_spec (a b : Array Digit) (len : Nat) :
    (addLoop a b len).1.size = len ∧ (addLoop a b len).2.toNat ≤ 1 ∧
      denote (addLoop a b len).1 + (addLoop a b len).2.toNat * base ^ len
        = denoteN a len + denoteN b len := by
  induction len with
  | zero => exact ⟨rfl, Nat.zero_le _, rfl⟩
  | succ len ih =>
    obtain ⟨hsz, hk, hval⟩ := ih
    have hstep : addLoop a b (len+1) = addStep a b (addLoop a b len) len := by
      simp [addLoop, List.range_succ, List.foldl_append]
    rw [hstep]
    refine ⟨by simp [addStep, hsz], addStep_carry_le .., ?_⟩
    have hd := addStep_digit (a.getD len 0) (b.getD len 0) (addLoop a b len).2 hk
    show denote ((addLoop a b len).1.push _) + _ * base ^ (len+1) = _
    rw [show denoteN a (len+1) = denoteN a len + (a.getD len 0).toNat * base ^ len from rfl,
        show denoteN b (len+1) = denoteN b len + (b.getD len 0).toNat * base ^ len from rfl,
        denote_push, hsz, Nat.pow_succ]
    exact add_combine hval hd

theorem denote_trim (c : Array Digit) : denote (trim c) = denote c := by
  unfold trim
  split <;> rename_i h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rw [denote_trim c.pop, denote_pop_of_back_zero c (by omega) h.2]
  · rfl
termination_by c.size
decreasing_by simp_all; omega

/-- `mpn_add` computes the sum. -/
theorem denote_add (a b : Array Digit) : denote (add a b) = denote a + denote b := by
  obtain ⟨hsz, _, hval⟩ := addLoop_spec a b (max a.size b.size)
  simp only [add, denote_trim, denote_push, hsz]
  rw [hval, denoteN_of_ge a (Nat.le_max_left ..), denoteN_of_ge b (Nat.le_max_right ..)]

/-! ## Correctness of `mpn_sub` -/

/-- The digit-level borrow identity: `c[j] + v_j + k = u_j + borrow * 2^32`. -/
theorem subStep_digit (u v k : Digit) (hk : k.toNat ≤ 1) :
    ((u - v) - k).toNat + v.toNat + k.toNat
      = u.toNat + (if (u - v) > u || ((u - v) - k) > (u - v) then (1 : Digit) else 0).toNat * base := by
  have hsz : (UInt32.size : Nat) = 4294967296 := rfl
  have hu := UInt32.toNat_lt_size u
  have hv := UInt32.toNat_lt_size v
  simp only [base]
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
      simp [subLoop, List.range_succ, List.foldl_append]
    rw [hstep]
    refine ⟨by simp [subStep, hsz], subStep_borrow_le .., ?_⟩
    have hd := subStep_digit (a.getD len 0) (b.getD len 0) (subLoop a b len).2 hk
    show denote ((subLoop a b len).1.push _) + _ = _
    rw [show denoteN a (len+1) = denoteN a len + (a.getD len 0).toNat * base ^ len from rfl,
        show denoteN b (len+1) = denoteN b len + (b.getD len 0).toNat * base ^ len from rfl,
        denote_push, hsz, Nat.pow_succ]
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
  simpa only [sub, denoteN_of_ge a (Nat.le_max_left ..),
    denoteN_of_ge b (Nat.le_max_right ..)] using hval

/-! ## Correctness of `mpn_mul` -/

/-- Splitting a 64-bit accumulator into its two digits loses nothing. -/
theorem lo_add_hi (t : DoubleDigit) : (lo t).toNat + (hi t).toNat * base = t.toNat := by
  have h := UInt64.toNat_lt_size t
  have hs : (UInt64.size : Nat) = 18446744073709551616 := rfl
  have h32 : (UInt64.toNat 32 % 64) = 32 := rfl
  simp only [lo, hi, base, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hs, h32,
    Nat.shiftRight_eq_div_pow] at *
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
  rw [hs] at hx hy hz hw
  have hb : x.toNat * y.toNat ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt32.toNat_toUInt64]
  omega

private theorem mulInner_combine {dc k p P Q ai v dc0 dna c0ij B lot hit : Nat}
    (hp : p = P * Q)
    (hval : dc + k * p = dc0 + dna * v * P)
    (hdig : lot + hit * B = ai * v + c0ij + k) :
    dc + lot * p + hit * (p * B) = dc0 + c0ij * p + (dna + ai * Q) * v * P := by
  subst hp; grind

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
      simp [mulInner, List.range_succ, List.foldl_append]
    -- the digit this step reads has not been written yet
    have hread : (mulInner a v j c₀ n).1.getD (n + j) 0 = c₀.getD (n + j) 0 :=
      huntouched _ (Or.inr (by omega))
    have hlt : n + j < (mulInner a v j c₀ n).1.size := by rw [hsz]; omega
    rw [hstep]
    simp only [mulInnerStep, hread]
    refine ⟨by simp [hsz], ?_, ?_⟩
    · intro idx hidx
      rw [getD_set!_ne _ _ _ _ (by omega), huntouched idx (by omega)]
    · rw [show j + (n+1) = (n + j) + 1 by omega, denoteN_set!_succ _ _ _ hlt,
        show denoteN c₀ ((n+j)+1)
            = denoteN c₀ (n+j) + (c₀.getD (n+j) 0).toNat * base ^ (n+j) from rfl,
        show denoteN a (n+1) = denoteN a n + (a.getD n 0).toNat * base ^ n from rfl,
        show n + j = j + n by omega, Nat.pow_succ]
      exact mulInner_combine (Nat.pow_add base j n) hval
        (by rw [lo_add_hi, mulStep_toNat, show j + n = n + j by omega])

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
    refine ⟨by simp [mulLoop], fun idx _ => ?_, ?_⟩
    · rw [mulLoop, List.range_zero, List.foldl_nil]; exact getD_replicate_zero _ _
    · rw [mulLoop, List.range_zero, List.foldl_nil, denote_replicate_zero]; rfl
  | succ m ih =>
    obtain ⟨hsz, hzero, hval⟩ := ih (by omega)
    have hstep : mulLoop a b (m+1) = mulOuterStep a b (mulLoop a b m) m := by
      simp [mulLoop, List.range_succ, List.foldl_append]
    have hb : denoteN b (m+1) = denoteN b m + (b.getD m 0).toNat * base ^ m := rfl
    have hfits : m + a.size < (mulLoop a b m).size := by rw [hsz]; omega
    rw [hstep]
    simp only [mulOuterStep]
    split <;> rename_i hv
    · -- `v_j == 0`: the digit about to be written is already zero
      have hv0 : (b.getD m 0).toNat = 0 := by
        simp only [beq_iff_eq] at hv; rw [hv]; rfl
      have hsame : ∀ i, i < (mulLoop a b m).size →
          ((mulLoop a b m).set! (m + a.size) 0).getD i 0 = (mulLoop a b m).getD i 0 := by
        intro i _
        rcases Nat.decEq i (m + a.size) with h | h
        · exact getD_set!_ne _ _ _ _ h
        · subst h; rw [getD_set!_eq _ _ _ hfits, hzero _ (Nat.le_refl _)]
      refine ⟨by simp [hsz], ?_, ?_⟩
      · intro idx hidx
        rw [getD_set!_ne _ _ _ _ (by omega), hzero idx (by omega)]
      · rw [hb, hv0, Nat.zero_mul, Nat.add_zero, ← hval, denote, denote,
          Array.size_set!]
        exact denoteN_congr hsame
    · -- the general case: run the inner loop, then store its carry
      obtain ⟨hisz, hiunt, hival⟩ := mulInner_spec a (b.getD m 0) m (mulLoop a b m) a.size (by omega)
      have hcarry : m + a.size < (mulInner a (b.getD m 0) m (mulLoop a b m) a.size).1.size := by
        rw [hisz, hsz]; omega
      have hhigh : ∀ idx, (m + a.size) + 1 ≤ idx →
          (((mulInner a (b.getD m 0) m (mulLoop a b m) a.size).1).set! (m + a.size)
            (mulInner a (b.getD m 0) m (mulLoop a b m) a.size).2).getD idx 0 = 0 := by
        intro idx hidx
        rw [getD_set!_ne _ _ _ _ (by omega), hiunt idx (Or.inr (by omega)), hzero idx (by omega)]
      refine ⟨by rw [Array.size_set!, hisz, hsz], ?_, ?_⟩
      · intro idx hidx
        exact hhigh idx (by omega)
      · rw [denote_of_high_zero _ (by rw [Array.size_set!, hisz, hsz]; omega) hhigh,
          denoteN_set!_succ _ _ _ hcarry, hival,
          ← denote_of_high_zero (mulLoop a b m) (by rw [hsz]; omega)
            (fun idx h => hzero idx (by omega)),
          hval, hb]
        show denote a * denoteN b m + denote a * (b.getD m 0).toNat * base ^ m
            = denote a * (denoteN b m + (b.getD m 0).toNat * base ^ m)
        rw [Nat.mul_add, Nat.mul_assoc]

/-- `mpn_mul` computes the product. -/
theorem denote_mul (a b : Array Digit) : denote (mul a b) = denote a * denote b :=
  (mulLoop_spec a b b.size (Nat.le_refl _)).2.2

/-- `mpn_mul` writes exactly `lnga + lngb` digits, as its callers assume. -/
theorem size_mul (a b : Array Digit) : (mul a b).size = a.size + b.size :=
  (mulLoop_spec a b b.size (Nat.le_refl _)).1

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
  have hpow : b ^ (k+1) = b ^ k * b := Nat.pow_succ b k
  -- `qhat` times the divisor's leading part already fits under `u`
  have hmain : qhat * ((vtop * b + vsnd) * b ^ k) ≤ u := by
    calc qhat * ((vtop * b + vsnd) * b ^ k)
        = qhat * vtop * (b ^ k * b) + (qhat * vsnd) * b ^ k := by grind
      _ ≤ qhat * vtop * (b ^ k * b) + (b * rhat + u3) * b ^ k :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hfail) _
      _ = u2 * (b ^ k * b) + u3 * b ^ k := by rw [hu2]; grind
      _ ≤ u := by rw [hu, hpow]; omega
  -- and the low part of the divisor that this ignores is itself below the divisor
  have hslack : qhat * vrest ≤ (vtop * b + vsnd) * b ^ k + vrest := by
    have h1 : qhat * vrest ≤ b * b ^ k := Nat.mul_le_mul (by omega) (by omega)
    have h2 : b * b ^ k ≤ (vtop * b + vsnd) * b ^ k := by
      refine Nat.mul_le_mul_right _ ?_
      calc b = 1 * b := (Nat.one_mul b).symm
        _ ≤ vtop * b := Nat.mul_le_mul_right b hvtop
        _ ≤ vtop * b + vsnd := Nat.le_add_right _ _
    exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_add_right _ _)
  calc qhat * ((vtop * b + vsnd) * b ^ k + vrest)
      = qhat * ((vtop * b + vsnd) * b ^ k) + qhat * vrest := by grind
    _ ≤ u + ((vtop * b + vsnd) * b ^ k + vrest) := Nat.add_le_add hmain hslack

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

theorem toNat_shl (x : Digit) {d : Nat} (hd : d < digitBits) :
    (x <<< (UInt32.ofNat d)).toNat = (x.toNat * 2 ^ d) % base := by
  have hm : (UInt32.ofNat d).toNat % 32 = d := by simp [digitBits] at hd ⊢; omega
  rw [UInt32.toNat_shiftLeft, hm, Nat.shiftLeft_eq]
  rfl

theorem toNat_shr (y : Digit) {e : Nat} (he : e < digitBits) :
    (y >>> (UInt32.ofNat e)).toNat = y.toNat / 2 ^ e := by
  have hm : (UInt32.ofNat e).toNat % 32 = e := by simp [digitBits] at he ⊢; omega
  rw [UInt32.toNat_shiftRight, hm, Nat.shiftRight_eq_div_pow]

/--
Recombining two adjacent digits under a left shift by `d`: the `|` in
`div_normalize` cannot carry, because the low `d` bits of the shifted digit are
zero and the bits arriving from below are less than `2^d`.
-/
theorem toNat_shl_or_shr (x y : Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits) :
    ((x <<< (UInt32.ofNat d)) ||| (y >>> (UInt32.ofNat (digitBits - d)))).toNat
      = (x.toNat * 2 ^ d) % base + y.toNat / 2 ^ (digitBits - d) := by
  simp only [digitBits] at hd hd0 ⊢
  have hy : y.toNat < 2 ^ 32 := y.toNat_lt_size
  have hlt : y.toNat / 2 ^ (32 - d) < 2 ^ d := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show 32 - d + d = 32 by omega]
    exact hy
  have hsplit : (x.toNat * 2 ^ d) % base = (x.toNat % 2 ^ (32 - d)) <<< d := by
    have hb : base = 2 ^ (32 - d) * 2 ^ d := by
      rw [← Nat.pow_add, show 32 - d + d = 32 by omega]; rfl
    rw [hb, Nat.mul_mod_mul_right, Nat.shiftLeft_eq]
  rw [UInt32.toNat_or, toNat_shl x (by simp [digitBits]; omega),
    toNat_shr y (by simp [digitBits]; omega), hsplit, Nat.shiftLeft_add_eq_or_of_lt hlt]

/-- The bits that digit `j-1` sends up into digit `j` under a left shift by `d`. -/
private def shiftCarry (a : Array Digit) (d j : Nat) : Nat :=
  if j = 0 then 0 else (a.getD (j-1) 0).toNat / 2 ^ (digitBits - d)

private theorem shiftCarry_eq (a : Array Digit) {d j : Nat} (hd0 : 0 < d) (hd : d < digitBits)
    (hj : j ≠ 0) : shiftCarry a d j = (a.getD (j-1) 0).toNat * 2 ^ d / base := by
  simp only [shiftCarry, hj, ite_false, digitBits] at *
  have hb : base = 2 ^ (32 - d) * 2 ^ d := by
    rw [← Nat.pow_add, show 32 - d + d = 32 by omega]; rfl
  rw [hb, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos d)]

private theorem getD_shiftLeftDigits_zero (a : Array Digit) (len j : Nat) (hj : j < len) :
    (shiftLeftDigits a 0 len).getD j 0 = a.getD j 0 := by
  simp [shiftLeftDigits, hj]

private theorem getD_shiftLeftDigits_head (a : Array Digit) {d len : Nat} (hd0 : 0 < d)
    (hlen : 0 < len) :
    (shiftLeftDigits a d len).getD 0 0 = a.getD 0 0 <<< UInt32.ofNat d := by
  simp [shiftLeftDigits, hlen, Nat.ne_of_gt hd0]

private theorem getD_shiftLeftDigits_tail (a : Array Digit) {d len j : Nat} (hd0 : 0 < d)
    (hj : j < len) (hj0 : j ≠ 0) :
    (shiftLeftDigits a d len).getD j 0
      = (a.getD j 0 <<< UInt32.ofNat d) ||| (a.getD (j-1) 0 >>> UInt32.ofNat (digitBits - d)) := by
  simp [shiftLeftDigits, hj, Nat.ne_of_gt hd0, hj0]

private theorem shift_combine {Oj C C' P Dj A B T : Nat}
    (hih : Oj + C * P = Dj * T)
    (hdm : A * T % B + B * (A * T / B) = A * T)
    (hC' : C' = A * T / B) :
    Oj + (A * T % B + C) * P + C' * (P * B) = (Dj + A * P) * T := by
  subst hC'; grind

/-- The shifted digits denote `2^d` times the original, modulo what falls off the top. -/
theorem denoteN_shiftLeftDigits (a : Array Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits)
    {len j : Nat} (hj : j ≤ len) :
    denoteN (shiftLeftDigits a d len) j + shiftCarry a d j * base ^ j = denoteN a j * 2 ^ d := by
  induction j with
  | zero => simp [denoteN, shiftCarry]
  | succ j ih =>
    have hdigit : ((shiftLeftDigits a d len).getD j 0).toNat
        = (a.getD j 0).toNat * 2 ^ d % base + shiftCarry a d j := by
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        rw [getD_shiftLeftDigits_head a hd0 (by omega), toNat_shl _ hd]
        simp [shiftCarry]
      · rw [getD_shiftLeftDigits_tail a hd0 (by omega) (by omega), toNat_shl_or_shr _ _ hd0 hd]
        simp only [shiftCarry, Nat.ne_of_gt hj0, ite_false]
    have hC' : shiftCarry a d (j+1) = (a.getD j 0).toNat * 2 ^ d / base := by
      rw [shiftCarry_eq a hd0 hd (Nat.succ_ne_zero j)]; simp
    have hdm := Nat.div_add_mod ((a.getD j 0).toNat * 2 ^ d) base
    rw [denoteN, denoteN, hdigit, Nat.pow_succ]
    exact shift_combine (ih (by omega)) (by omega) hC'

theorem size_shiftLeftDigits (a : Array Digit) (d len : Nat) :
    (shiftLeftDigits a d len).size = len := by simp [shiftLeftDigits]

/--
A left shift by `d` bits multiplies the denotation by `2^d`, provided the result
still fits in `len` digits. `div_normalize` gives the numerator one extra digit
for exactly this reason, and chooses `d` so the denominator does not overflow.
-/
theorem denote_shiftLeftDigits (a : Array Digit) {d : Nat} (hd : d < digitBits)
    {len : Nat} (hlen : a.size ≤ len) (hfit : denote a * 2 ^ d < base ^ len) :
    denote (shiftLeftDigits a d len) = denote a * 2 ^ d := by
  have hout : denote (shiftLeftDigits a d len) = denoteN (shiftLeftDigits a d len) len := by
    rw [denote, size_shiftLeftDigits]
  have ha : denoteN a len = denote a := denoteN_of_ge a hlen
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    have hcongr : ∀ i, i < len → (shiftLeftDigits a 0 len).getD i 0 = a.getD i 0 := by
      intro i hi; exact getD_shiftLeftDigits_zero a len i hi
    rw [hout, denoteN_congr hcongr, ha]; simp
  · have hmain := denoteN_shiftLeftDigits a hd0 hd (Nat.le_refl len)
    rw [ha] at hmain
    -- nothing can fall off the top, so the carry out of the last digit is zero
    have hzero : shiftCarry a d len = 0 := by
      rcases Nat.eq_zero_or_pos (shiftCarry a d len) with h | h
      · exact h
      · exact absurd hmain (by
          have : base ^ len ≤ shiftCarry a d len * base ^ len := Nat.le_mul_of_pos_left _ h
          omega)
    rw [hzero, Nat.zero_mul, Nat.add_zero] at hmain
    rw [hout, hmain]

/-! ## Correctness of `div_normalize`'s shift amount -/

private theorem and_top_eq_zero_iff {y : Nat} (hy : y < 4294967296) :
    (y &&& 2147483648 = 0) ↔ y < 2147483648 := by
  have hpow : (2147483648 : Nat) = 2 ^ 31 := by rfl
  constructor
  · intro h
    have hb : y.testBit 31 = false := by
      by_cases hb : y.testBit 31
      · exfalso
        have hand : (y &&& 2147483648).testBit 31 = true := by
          rw [Nat.testBit_and, hb, hpow, Nat.testBit_two_pow_self]; rfl
        rw [h] at hand; simp at hand
      · simpa using hb
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    simp only [decide_eq_false_iff_not] at hb
    have h2 : y / 2 ^ 31 < 2 := by rw [← hpow] at *; omega
    rw [← hpow] at hb h2
    omega
  · intro h
    have hb : y.testBit 31 = false := Nat.testBit_lt_two_pow (by rw [← hpow]; exact h)
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit, hpow, Nat.testBit_two_pow]
    by_cases h31 : (31 : Nat) = i
    · subst h31; simp [hb]
    · simp [h31]

/-- `div_normalize`'s `(x << d) & MASK_FIRST == 0` test reads the top bit. -/
private theorem topBit_test (y : Digit) :
    (y &&& maskFirst == 0) = decide (y.toNat < 2147483648) := by
  have hy : y.toNat < 4294967296 := y.toNat_lt_size
  have hand : (y &&& maskFirst).toNat = y.toNat &&& 2147483648 := by
    rw [UInt32.toNat_and]; rfl
  have hiff : (y &&& maskFirst = 0) ↔ y.toNat < 2147483648 := by
    constructor
    · intro h
      have h0 : (y &&& maskFirst).toNat = 0 := by rw [h]; rfl
      rw [hand] at h0
      exact (and_top_eq_zero_iff hy).mp h0
    · intro h
      have h0 : y.toNat &&& 2147483648 = 0 := (and_top_eq_zero_iff hy).mpr h
      rw [← hand] at h0
      exact UInt32.toNat_inj.mp (by rw [h0]; rfl)
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact hiff

private theorem countWhile_le (p : Nat → Bool) (fuel i : Nat) : countWhile p fuel i ≤ fuel := by
  induction fuel generalizing i with
  | zero => simp [countWhile]
  | succ fuel ih =>
    simp only [countWhile]
    split
    · have := ih (i+1); omega
    · omega

private theorem countWhile_holds (p : Nat → Bool) (fuel i j : Nat)
    (hj : j < countWhile p fuel i) : p (i + j) := by
  induction fuel generalizing i j with
  | zero => simp [countWhile] at hj
  | succ fuel ih =>
    simp only [countWhile] at hj
    split at hj <;> rename_i hp
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simpa using hp
      · have hstep := ih (i+1) (j-1) (by omega)
        rw [show i + 1 + (j - 1) = i + j by omega] at hstep
        exact hstep
    · omega

private theorem countWhile_stop (p : Nat → Bool) (fuel i : Nat)
    (h : countWhile p fuel i < fuel) : ¬ p (i + countWhile p fuel i) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    by_cases hp : p i
    · have hc : countWhile p (fuel+1) i = 1 + countWhile p fuel (i+1) := by simp [countWhile, hp]
      rw [hc] at h ⊢
      rw [show i + (1 + countWhile p fuel (i+1)) = i + 1 + countWhile p fuel (i+1) by omega]
      exact ih (i+1) (by omega)
    · have hc : countWhile p (fuel+1) i = 0 := by simp [countWhile, hp]
      rw [hc]; simpa using hp

/-- The predicate `leadingZeros` counts, in arithmetic terms. -/
private theorem leadingZeros_pred (x : Digit) {i : Nat} (hi : i < digitBits) :
    ((x <<< (UInt32.ofNat i)) &&& maskFirst == 0)
      = decide (x.toNat * 2 ^ i % base < 2147483648) := by
  rw [topBit_test, toNat_shl x hi]

/--
`div_normalize` shifts by exactly enough to set the top bit of the leading
denominator digit: the shifted digit lands in `[2^31, 2^32)`, which is what
normalization means and what Knuth's Algorithm D assumes of its divisor.
-/
theorem leadingZeros_spec (x : Digit) (hx : 0 < x.toNat) :
    leadingZeros x < digitBits ∧
      2147483648 ≤ x.toNat * 2 ^ leadingZeros x ∧ x.toNat * 2 ^ leadingZeros x < base := by
  have hxlt : x.toNat < base := x.toNat_lt_size
  have hdle : leadingZeros x ≤ digitBits := countWhile_le _ _ _
  -- every step the loop took means the value had not yet reached the top bit
  have hbelow : ∀ i, i < leadingZeros x → x.toNat * 2 ^ i < 2147483648 := by
    intro i
    induction i with
    | zero =>
      intro hlt
      have hp := countWhile_holds _ digitBits 0 0 (by simpa [leadingZeros] using hlt)
      rw [Nat.zero_add, leadingZeros_pred x (by omega)] at hp
      simp only [decide_eq_true_eq, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hxlt] at hp
      simpa using hp
    | succ i ih =>
      intro hlt
      have hprev := ih (by omega)
      have hfit : x.toNat * 2 ^ (i+1) < base := by
        rw [Nat.pow_succ, ← Nat.mul_assoc]; simp only [base]; omega
      have hp := countWhile_holds _ digitBits 0 (i+1) (by simpa [leadingZeros] using hlt)
      rw [Nat.zero_add, leadingZeros_pred x (by omega)] at hp
      simp only [decide_eq_true_eq, Nat.mod_eq_of_lt hfit] at hp
      exact hp
  have hdlt : leadingZeros x < digitBits := by
    rcases Nat.lt_or_ge (leadingZeros x) digitBits with h | h
    · exact h
    · exfalso
      have h31 := hbelow 31 (by simp only [digitBits] at h; omega)
      rw [show (2:Nat) ^ 31 = 2147483648 from rfl] at h31
      omega
  have hfit : x.toNat * 2 ^ leadingZeros x < base := by
    rcases Nat.eq_zero_or_pos (leadingZeros x) with h | h
    · rw [h]; simpa using hxlt
    · obtain ⟨m, hm⟩ : ∃ m, leadingZeros x = m + 1 := ⟨leadingZeros x - 1, by omega⟩
      have hprev := hbelow m (by omega)
      rw [hm, Nat.pow_succ, ← Nat.mul_assoc]
      simp only [base]; omega
  refine ⟨hdlt, ?_, hfit⟩
  have hstop : ¬ ((x <<< UInt32.ofNat (leadingZeros x)) &&& maskFirst == 0) := by
    have hs := countWhile_stop (fun i => (x <<< UInt32.ofNat i) &&& maskFirst == 0) digitBits 0
      (by simpa [leadingZeros] using hdlt)
    simpa [leadingZeros] using hs
  rw [leadingZeros_pred x hdlt] at hstop
  simp only [decide_eq_true_eq, Nat.not_lt, Nat.mod_eq_of_lt hfit] at hstop
  exact hstop

/-! ## Correctness of `div_normalize` -/

/-- Shifting a digit left can only add to it, never lose its own bits. -/
private theorem le_getD_shiftLeftDigits (a : Array Digit) {d len j : Nat} (hd : d < digitBits)
    (hj : j < len) :
    (a.getD j 0).toNat * 2 ^ d % base ≤ ((shiftLeftDigits a d len).getD j 0).toNat := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    rw [getD_shiftLeftDigits_zero a len j hj, Nat.pow_zero, Nat.mul_one]
    exact Nat.mod_le _ _
  · rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [getD_shiftLeftDigits_head a hd0 (by omega), toNat_shl _ hd]
      exact Nat.le_refl _
    · rw [getD_shiftLeftDigits_tail a hd0 hj (by omega), toNat_shl_or_shr _ _ hd0 hd]
      exact Nat.le_add_right _ _

/-- Under the preconditions every caller satisfies, `div_normalize` shifts both operands. -/
private theorem divNormalize_eq (numer denom : Array Digit) (hnum : 0 < numer.size)
    (hden : 0 < denom.size) :
    divNormalize numer denom =
      (leadingZeros (denom.getD (denom.size - 1) 0),
       shiftLeftDigits numer (leadingZeros (denom.getD (denom.size - 1) 0)) (numer.size + 1),
       shiftLeftDigits denom (leadingZeros (denom.getD (denom.size - 1) 0)) denom.size) := by
  simp only [divNormalize, Nat.ne_of_gt hden, ite_false, Nat.ne_of_gt hnum,
    Bool.false_and, decide_false, ite_false]
  rfl

/--
`div_normalize`. The numerator gains a digit and both operands are multiplied by
`2^d`, where `d` is chosen so the leading denominator digit ends up with its top
bit set, which is what Knuth's Algorithm D assumes of its divisor.
-/
theorem divNormalize_spec (numer denom : Array Digit) (hnum : 0 < numer.size)
    (hden : 0 < denom.size) (htop : 0 < (denom.getD (denom.size - 1) 0).toNat) :
    (divNormalize numer denom).1 < digitBits ∧
    (divNormalize numer denom).2.1.size = numer.size + 1 ∧
    (divNormalize numer denom).2.2.size = denom.size ∧
    denote (divNormalize numer denom).2.1 = denote numer * 2 ^ (divNormalize numer denom).1 ∧
    denote (divNormalize numer denom).2.2 = denote denom * 2 ^ (divNormalize numer denom).1 ∧
    2147483648 ≤ ((divNormalize numer denom).2.2.getD (denom.size - 1) 0).toNat := by
  obtain ⟨hdlt, hlo, hhi⟩ := leadingZeros_spec (denom.getD (denom.size - 1) 0) htop
  rw [divNormalize_eq numer denom hnum hden]
  dsimp only
  refine ⟨hdlt, size_shiftLeftDigits .., size_shiftLeftDigits .., ?_, ?_, ?_⟩
  · -- the numerator has a spare digit, so `2^d < base` is room enough
    refine denote_shiftLeftDigits numer hdlt (by omega) ?_
    have h1 : denote numer < base ^ numer.size := denoteN_lt numer numer.size
    have h2 : (2:Nat) ^ (leadingZeros (denom.getD (denom.size - 1) 0)) ≤ base := by
      calc (2:Nat) ^ (leadingZeros (denom.getD (denom.size - 1) 0)) ≤ 2 ^ 32 :=
            Nat.pow_le_pow_right (by omega) (by simp only [digitBits] at hdlt; omega)
        _ = base := rfl
    calc denote numer * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0))
        < base ^ numer.size * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
      _ ≤ base ^ numer.size * base := Nat.mul_le_mul_left _ h2
      _ = base ^ (numer.size + 1) := (Nat.pow_succ base numer.size).symm
  · -- the denominator has no spare digit; `d` was chosen so it does not need one
    refine denote_shiftLeftDigits denom hdlt (Nat.le_refl _) ?_
    have hsplit : denote denom
        < ((denom.getD (denom.size - 1) 0).toNat + 1) * base ^ (denom.size - 1) := by
      have hlow : denoteN denom (denom.size - 1) < base ^ (denom.size - 1) :=
        denoteN_lt denom (denom.size - 1)
      have hden' : denote denom = denoteN denom (denom.size - 1)
          + (denom.getD (denom.size - 1) 0).toNat * base ^ (denom.size - 1) := by
        obtain ⟨m, hm⟩ : ∃ m, denom.size = m + 1 := ⟨denom.size - 1, by omega⟩
        rw [denote, hm, Nat.add_sub_cancel]
        rfl
      rw [hden', Nat.add_mul, Nat.one_mul]
      omega
    -- `t * 2^d < base` forces `(t + 1) * 2^d ≤ base`
    have hstep : ((denom.getD (denom.size - 1) 0).toNat + 1)
        * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)) ≤ base := by
      have hd32 : leadingZeros (denom.getD (denom.size - 1) 0) < 32 := by
        simp only [digitBits] at hdlt; omega
      have hb : base = 2 ^ (32 - leadingZeros (denom.getD (denom.size - 1) 0))
          * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)) := by
        rw [← Nat.pow_add, show 32 - leadingZeros (denom.getD (denom.size - 1) 0)
          + leadingZeros (denom.getD (denom.size - 1) 0) = 32 by omega]; rfl
      have hlt : (denom.getD (denom.size - 1) 0).toNat
          < 2 ^ (32 - leadingZeros (denom.getD (denom.size - 1) 0)) := by
        refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ leadingZeros (denom.getD (denom.size - 1) 0)) ?_
        rw [← hb]; exact hhi
      calc ((denom.getD (denom.size - 1) 0).toNat + 1)
            * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0))
          ≤ 2 ^ (32 - leadingZeros (denom.getD (denom.size - 1) 0))
            * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = base := hb.symm
    calc denote denom * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0))
        < ((denom.getD (denom.size - 1) 0).toNat + 1) * base ^ (denom.size - 1)
            * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0)) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hsplit
      _ = (((denom.getD (denom.size - 1) 0).toNat + 1)
            * 2 ^ (leadingZeros (denom.getD (denom.size - 1) 0))) * base ^ (denom.size - 1) := by
          grind
      _ ≤ base * base ^ (denom.size - 1) := Nat.mul_le_mul_right _ hstep
      _ = base ^ denom.size := by
          rw [Nat.mul_comm, ← Nat.pow_succ]
          congr 1
          omega
  · -- the shifted leading digit keeps the bits `leadingZeros` put in place
    have hle := le_getD_shiftLeftDigits denom (d := leadingZeros (denom.getD (denom.size - 1) 0))
      (len := denom.size) (j := denom.size - 1) hdlt (by omega)
    rw [Nat.mod_eq_of_lt hhi] at hle
    omega

/-! ## Correctness of `div_unnormalize` -/

theorem toNat_lastBits (x : Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits) :
    (lastBits x d).toNat = x.toNat % 2 ^ d := by
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
  have hd' : d < 32 := by simpa [digitBits] using hd
  rw [lastBits, toNat_shr _ (by simp [digitBits]; omega), toNat_shl _ (by simp [digitBits]; omega)]
  simp only [digitBits]
  have hb : base = 2 ^ d * 2 ^ (32 - d) := by
    rw [← Nat.pow_add, show d + (32 - d) = 32 by omega]; rfl
  rw [hb, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos (32 - d))]

/--
Recombining two adjacent digits under a right shift by `d`: as with the left
shift, the `|` cannot carry, since `a[i] >> d` is below `2^(32-d)` and the bits
arriving from above are a multiple of it.
-/
theorem toNat_shr_or_shl (x y : Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits) :
    ((x >>> (UInt32.ofNat d)) ||| (lastBits y d <<< (UInt32.ofNat (digitBits - d)))).toNat
      = x.toNat / 2 ^ d + y.toNat % 2 ^ d * 2 ^ (digitBits - d) := by
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
  have hlow : x.toNat / 2 ^ d < 2 ^ (digitBits - d) := by
    simp only [digitBits] at hd hd0 ⊢
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show d + (32 - d) = 32 by omega]
    exact hx
  have hhigh : (lastBits y d <<< (UInt32.ofNat (digitBits - d))).toNat
      = (y.toNat % 2 ^ d) <<< (digitBits - d) := by
    rw [toNat_shl _ (by simp only [digitBits] at hd0 ⊢; omega), toNat_lastBits y hd0 hd,
      Nat.shiftLeft_eq]
    refine Nat.mod_eq_of_lt ?_
    simp only [digitBits] at hd hd0 ⊢
    calc y.toNat % 2 ^ d * 2 ^ (32 - d) < 2 ^ d * 2 ^ (32 - d) :=
          Nat.mul_lt_mul_right (Nat.two_pow_pos _) |>.mpr (Nat.mod_lt _ (Nat.two_pow_pos d))
      _ = base := by rw [← Nat.pow_add, show d + (32 - d) = 32 by omega]; rfl
  rw [UInt32.toNat_or, hhigh, toNat_shr _ (by simp only [digitBits] at hd ⊢; omega),
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlow, Nat.shiftLeft_eq, Nat.add_comm]

private theorem getD_shiftRightDigits_zero (a : Array Digit) (len j : Nat) (hj : j < len) :
    (shiftRightDigits a 0 len).getD j 0 = a.getD j 0 := by
  simp [shiftRightDigits, hj]

private theorem getD_shiftRightDigits_last (a : Array Digit) {d len : Nat} (hd0 : 0 < d)
    (hlen : 0 < len) :
    (shiftRightDigits a d len).getD (len - 1) 0 = a.getD (len - 1) 0 >>> UInt32.ofNat d := by
  simp [shiftRightDigits, Nat.ne_of_gt hd0, show len - 1 < len by omega, show len - 1 + 1 = len by omega]

private theorem getD_shiftRightDigits_mid (a : Array Digit) {d len j : Nat} (hd0 : 0 < d)
    (hj : j < len) (hj' : j + 1 ≠ len) :
    (shiftRightDigits a d len).getD j 0
      = (a.getD j 0 >>> UInt32.ofNat d) |||
        (lastBits (a.getD (j+1) 0) d <<< UInt32.ofNat (digitBits - d)) := by
  simp [shiftRightDigits, Nat.ne_of_gt hd0, hj, hj']

private theorem shiftRight_combine {Rj rj xj xj1 P T U B Nj lo0 : Nat}
    (hB : U * T = B)
    (hih : Rj * T + lo0 = Nj + xj % T * P)
    (hrj : rj = xj / T + xj1 % T * U)
    (hdm : xj % T + T * (xj / T) = xj) :
    (Rj + rj * P) * T + lo0 = Nj + xj * P + xj1 % T * (P * B) := by
  subst hrj hB; grind

theorem size_shiftRightDigits (a : Array Digit) (d len : Nat) :
    (shiftRightDigits a d len).size = len := by simp [shiftRightDigits]

/--
The loop invariant of the right shift: the digits written so far, scaled back up
by `2^d` and given the bits that fell off the bottom, account for the digits of
`a` they were built from, up to the bits digit `j` still owes downward.
-/
theorem denoteN_shiftRightDigits (a : Array Digit) {d : Nat} (hd0 : 0 < d) (hd : d < digitBits)
    {len j : Nat} (hj : j < len) :
    denoteN (shiftRightDigits a d len) j * 2 ^ d + (a.getD 0 0).toNat % 2 ^ d
      = denoteN a j + (a.getD j 0).toNat % 2 ^ d * base ^ j := by
  induction j with
  | zero => simp [denoteN]
  | succ j ih =>
    have hmid : ((shiftRightDigits a d len).getD j 0).toNat
        = (a.getD j 0).toNat / 2 ^ d + (a.getD (j+1) 0).toNat % 2 ^ d * 2 ^ (digitBits - d) := by
      rw [getD_shiftRightDigits_mid a hd0 (by omega) (by omega), toNat_shr_or_shl _ _ hd0 hd]
    have hB : 2 ^ (digitBits - d) * 2 ^ d = base := by
      simp only [digitBits] at hd hd0 ⊢
      rw [← Nat.pow_add, show 32 - d + d = 32 by omega]; rfl
    have hdm := Nat.div_add_mod (a.getD j 0).toNat (2 ^ d)
    rw [denoteN, denoteN, Nat.pow_succ]
    exact shiftRight_combine hB (ih (by omega)) hmid (by omega)

/--
`div_unnormalize` divides the denotation by `2^d`, undoing what
`div_normalize` did to the numerator and leaving the true remainder.
-/
theorem denote_shiftRightDigits (a : Array Digit) {d : Nat} (hd : d < digitBits) {len : Nat}
    (hlen : 0 < len) :
    denote (shiftRightDigits a d len) = denoteN a len / 2 ^ d := by
  have hsize : (shiftRightDigits a d len).size = len := size_shiftRightDigits ..
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    have hcongr : ∀ i, i < len → (shiftRightDigits a 0 len).getD i 0 = a.getD i 0 :=
      fun i hi => getD_shiftRightDigits_zero a len i hi
    rw [denote, hsize, denoteN_congr hcongr]
    simp
  · have hlast : ((shiftRightDigits a d len).getD (len-1) 0).toNat
        = (a.getD (len-1) 0).toNat / 2 ^ d := by
      rw [getD_shiftRightDigits_last a hd0 hlen, toNat_shr _ hd]
    have hinv := denoteN_shiftRightDigits a hd0 hd (len := len) (j := len - 1) (by omega)
    have hdm := Nat.div_add_mod (a.getD (len-1) 0).toNat (2 ^ d)
    have hlo : (a.getD 0 0).toNat % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
    -- fold the last digit in, which owes nothing downward
    have hfull : denote (shiftRightDigits a d len) * 2 ^ d + (a.getD 0 0).toNat % 2 ^ d
        = denoteN a len := by
      have hexp : denote (shiftRightDigits a d len)
          = denoteN (shiftRightDigits a d len) (len-1)
            + ((shiftRightDigits a d len).getD (len-1) 0).toNat * base ^ (len-1) := by
        obtain ⟨m, hm⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
        rw [denote, hsize, hm, Nat.add_sub_cancel]; rfl
      have hexpa : denoteN a len
          = denoteN a (len-1) + (a.getD (len-1) 0).toNat * base ^ (len-1) := by
        obtain ⟨m, hm⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel]; rfl
      rw [hexp, hlast, hexpa, Nat.add_mul]
      have : (a.getD (len-1) 0).toNat / 2 ^ d * base ^ (len-1) * 2 ^ d
          + (a.getD (len-1) 0).toNat % 2 ^ d * base ^ (len-1)
          = (a.getD (len-1) 0).toNat * base ^ (len-1) := by grind
      omega
    rw [← hfull, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos d),
      Nat.div_eq_of_lt hlo, Nat.add_zero]

/-!
## Differential testing against `Nat`

`mpn_compare`, `mpn_div` and `mpn_to_string` are not proved here; they are
checked against `Nat` on pseudorandom inputs instead, as are the proved
routines. The digit generator is biased towards `0`, `1` and `2^32-1` so that
carries, borrows and Knuth's quotient correction step fire often.
-/

namespace Test

/-- xorshift64. -/
def nextRand (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

def drawDigit (s : UInt64) : Digit × UInt64 :=
  let s := nextRand s
  let sel := (s >>> 59) % 8
  let d : Digit :=
    if sel == 0 then 0
    else if sel == 1 then 0xFFFFFFFF
    else if sel == 2 then 1
    else s.toUInt32
  (d, s)

def drawArray (n : Nat) (s : UInt64) : Array Digit × UInt64 := Id.run do
  let mut out : Array Digit := Array.emptyWithCapacity n
  let mut s := s
  for _ in [0:n] do
    let (d, s') := drawDigit s
    out := out.push d
    s := s'
  return (out, s)

/-- Every way one pair of operands can disagree with `Nat`. -/
def check (a b : Array Digit) : Array String := Id.run do
  let mut fs : Array String := #[]
  let ctx := s!"a={a.map (·.toNat)} b={b.map (·.toNat)}"
  let na := denote a
  let nb := denote b
  let len := max a.size b.size

  let c := compare a b
  let expected : Int := if na > nb then 1 else if na < nb then -1 else 0
  if c != expected then fs := fs.push s!"compare {ctx}: got {c}, expected {expected}"

  -- `mpn_add` asserts `len > 0`
  if len > 0 then
    let s := add a b
    if denote s != na + nb then fs := fs.push s!"add {ctx}: got {denote s}, expected {na + nb}"
    if s.size == 0 || s.size > len + 1 then
      fs := fs.push s!"add {ctx}: trimmed length {s.size} outside 1..{len+1}"
    if s.size > 1 && s.back! == 0 then
      fs := fs.push s!"add {ctx}: trimmed length leaves a redundant leading zero"

    -- `c = a - b + borrow * B^len`
    let (d, k) := sub a b
    if d.size != len then fs := fs.push s!"sub {ctx}: length {d.size}, expected {len}"
    if denote d + nb != na + k.toNat * base ^ len then
      fs := fs.push s!"sub {ctx}: digits {denote d}, borrow {k.toNat}"
    if (k != 0) != decide (na < nb) then
      fs := fs.push s!"sub {ctx}: borrow {k.toNat} but a<b is {decide (na < nb)}"

  let p := mul a b
  if p.size != a.size + b.size then
    fs := fs.push s!"mul {ctx}: length {p.size}, expected {a.size + b.size}"
  if denote p != na * nb then fs := fs.push s!"mul {ctx}: got {denote p}, expected {na * nb}"

  -- `mpn_div` requires `lden <= lnum` and a nonzero top denominator digit
  if b.size > 0 && b.size <= a.size && b.back! != 0 then
    let (q, r, stuck) := div a b
    if stuck then fs := fs.push s!"div {ctx}: div_n correction loop exhausted its fuel"
    if q.size != a.size - b.size + 1 then
      fs := fs.push s!"div {ctx}: quotient length {q.size}, expected {a.size - b.size + 1}"
    if r.size != b.size then
      fs := fs.push s!"div {ctx}: remainder length {r.size}, expected {b.size}"
    if denote q != na / nb then fs := fs.push s!"div {ctx}: quotient {denote q}, expected {na / nb}"
    if denote r != na % nb then fs := fs.push s!"div {ctx}: remainder {denote r}, expected {na % nb}"

  if a.size > 0 then
    let str := Mpn.toString a
    if str != ToString.toString na then
      fs := fs.push s!"toString {ctx}: got {str}, expected {na}"

  return fs

def run (trials : Nat) (seed : UInt64) (maxLen : Nat) : Array String := Id.run do
  let mut fs : Array String := #[]
  let mut s := seed
  for _ in [0:trials] do
    s := nextRand s
    let la := ((s >>> 33).toNat % maxLen) + 1
    s := nextRand s
    let lb := ((s >>> 33).toNat % maxLen) + 1
    let (a, s') := drawArray la s
    let (b, s'') := drawArray lb s'
    s := s''
    fs := fs ++ check a b
  return fs

/--
Print the results for `trials` operand pairs in the format
`mpn_model_crosscheck.cpp` uses, so that model and C++ can be diffed.
-/
def emit (trials : Nat) (maxLen : Nat) (seed : UInt64) : IO Unit := do
  let vec (tag : String) (v : Array Digit) : String :=
    v.foldl (fun acc d => acc ++ " " ++ ToString.toString d.toNat) tag
  let mut s := seed
  for t in [0:trials] do
    s := nextRand s
    let la := ((s >>> 33).toNat % maxLen) + 1
    s := nextRand s
    let lb := ((s >>> 33).toNat % maxLen) + 1
    let (a, s') := drawArray la s
    let (b, s'') := drawArray lb s'
    s := s''
    IO.println s!"case {t}"
    IO.println (vec "a" a)
    IO.println (vec "b" b)
    IO.println s!"compare {Mpn.compare a b}"
    IO.println (vec "add" (add a b))
    let (d, borrow) := sub a b
    IO.println (vec "sub" d)
    IO.println s!"borrow {borrow.toNat}"
    IO.println (vec "mul" (mul a b))
    if lb ≤ la && b.back! != 0 then
      let (q, r, _) := div a b
      IO.println (vec "quot" q)
      IO.println (vec "rem" r)
    IO.println s!"str {Mpn.toString a}"

end Test

/--
Cross-check every `mpn` routine against `Nat` on pseudorandom operands. The
trial counts are kept low enough to stay cheap in CI; raising them by two orders
of magnitude still reports no disagreement.
-/
def mpnCheck : IO Unit := do
  let mut failures := 0
  for (trials, maxLen, seed) in
      [(800, 3, 0x9E3779B97F4A7C15), (800, 6, 0x2545F4914F6CDD1D),
       (250, 10, 0xDEADBEEFCAFEBABE), (80, 20, 0x0123456789ABCDEF)] do
    let fs := Test.run trials seed maxLen
    failures := failures + fs.size
    for f in fs.extract 0 5 do IO.println f
  IO.println s!"mpn: {failures} disagreements with Nat"

end Mpn

#eval Mpn.mpnCheck
