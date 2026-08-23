/-!
# Lean transliteration of the runtime's GMP-free bignum core

`src/runtime/mpn.cpp` implements multi-precision naturals as little-endian
arrays of `uint32_t` digits. It is the arithmetic Lean uses when built with
`USE_GMP=OFF` (the 32-bit and WebAssembly targets); both of those CI
configurations are currently disabled, so the code has no automated coverage.

The kernel reaches it: `type_checker::reduce_nat` reduces `Nat.add`, `sub`,
`mul`, `pow`, `gcd`, `div`, `mod`, `beq` and `ble` through `mpz` and hence
through every routine here except `mpn_to_string`, whose only caller is
printing.

This file transliterates it statement by statement so that the algorithms can
be checked against `Nat`, which is what `#eval mpnCheck` at the bottom does, and
so that they can be proved correct: `denote_add`, `denote_sub`, `denote_mul`
`div_spec` and `compare_spec` do that for `mpn_add`, `mpn_sub`, `mpn_mul`,
`mpn_div` (by way of Knuth's Algorithm D) and `mpn_compare`. Deviations from the
C++ are marked `NOTE:`.

A transliteration is only worth as much as its fidelity to the original, so
`Mpn.Test.emit` prints the model's results in the format that
`mpn_model_crosscheck.cpp` prints the real `mpn.cpp`'s in, and `Mpn.Test.emitNum`
does the same against `mpz_crosscheck.cpp` for the `mpz` layer below. On the
same pseudorandom operands both agree byte for byte.
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

/-- `mpn_compare`'s loop, scanning digits from `j-1` down to 0. -/
def compareLoop (a b : Array Digit) : Nat → Int
  | 0 => 0
  | j+1 =>
    let u_j := a.getD j 0
    let v_j := b.getD j 0
    if u_j > v_j then 1 else if u_j < v_j then -1 else compareLoop a b j

/--
`mpn_compare`. The C++ latches `res` and runs the loop to completion; stopping
at the first difference is observationally the same.
-/
def compare (a b : Array Digit) : Int := compareLoop a b (max a.size b.size)

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

/-- One iteration of `div_1`'s loop, dividing the two-digit window at `j` by `denom`. -/
def div1Step (denom : Digit) (s : Array Digit × Array Digit) (j : Nat) :
    Array Digit × Array Digit :=
  let (u, quot) := s
  let temp : DoubleDigit := ((u.getD j 0).toUInt64 <<< 32) ||| (u.getD (j-1) 0).toUInt64
  let q_hat := temp / denom.toUInt64
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

/-- `div_1`'s loop, running from digit `j` down to digit 1. -/
def div1Loop (denom : Digit) (u quot : Array Digit) : Nat → Array Digit × Array Digit
  | 0 => (u, quot)
  | j+1 =>
    let s := div1Step denom (u, quot) (j+1)
    div1Loop denom s.1 s.2 j

/--
`div_1`. Single-digit division; returns the updated numerator (holding the
remainder in its lowest digit) and `numer.size - 1` quotient digits.
-/
def div1 (numer : Array Digit) (denom : Digit) : Array Digit × Array Digit :=
  div1Loop denom numer (Array.replicate (numer.size - 1) 0) (numer.size - 1)

/--
The `recheck:` correction loop of `div_n`, i.e. step D3 of Knuth's Algorithm D.

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

/-- `for i in [0:len] do dst := dst.set! (j+i) src[i]!` -/
def copyInto (dst src : Array Digit) (j : Nat) : Nat → Array Digit
  | 0 => dst
  | len+1 => (copyInto dst src j len).set! (j + len) (src.getD len 0)

/-- The trial quotient digit `div_n` forms for the window at `j`, after step D3. -/
def divNTrial (denom u : Array Digit) (j : Nat) : Digit :=
  let n := denom.size
  let temp : DoubleDigit :=
    ((u.getD (j+n) 0).toUInt64 <<< 32) ||| (u.getD (j+n-1) 0).toUInt64
  lo (recheck (denom.getD (n-1) 0) (denom.getD (n-2) 0) (u.getD (j+n-2) 0)
      (temp / (denom.getD (n-1) 0).toUInt64) (temp % (denom.getD (n-1) 0).toUInt64)).1

/-- One iteration of `div_n`'s outer loop, producing quotient digit `j`. -/
def divNStep (denom : Array Digit) (s : Array Digit × Array Digit) (j : Nat) :
    Array Digit × Array Digit :=
  let (u, quot) := s
  let n := denom.size
  let q_hat_small := divNTrial denom u j
  let ms := mul #[q_hat_small] denom
  let (diff, borrow) := sub (u.extract j (j+n+1)) ms
  let u := copyInto u diff j (n+1)
  if borrow != 0 then
    -- step D6: the estimate was one too high, so add the divisor back
    let ab := add denom (u.extract j (j+n+1))
    (copyInto u ab j (n+1), quot.set! j (q_hat_small - 1))
  else (u, quot.set! j q_hat_small)

/-- `div_n`'s outer loop, running from quotient digit `m-1` down to digit 0. -/
def divNLoop (denom : Array Digit) (u quot : Array Digit) : Nat → Array Digit × Array Digit
  | 0 => (u, quot)
  | m+1 =>
    let s := divNStep denom (u, quot) m
    divNLoop denom s.1 s.2 m

/--
`div_n`, i.e. Knuth's Algorithm D. Returns the updated numerator (holding the
normalized remainder) and `m` quotient digits.
-/
def divN (numer denom : Array Digit) : Array Digit × Array Digit :=
  divNLoop denom numer (Array.replicate (numer.size - denom.size) 0) (numer.size - denom.size)

/--
`mpn_div`. Returns `lnum - lden + 1` quotient digits and `lden` remainder digits.

NOTE: the `lnum < lden` branch of the C++ computes its loop bound
`lnum - lden + 1` in `size_t`, which underflows to `SIZE_MAX` whenever
`lden > lnum + 1` and then overruns the quotient buffer. Every in-tree caller
checks `lden <= lnum` first, so the branch is dead; the model returns an empty
quotient there.
-/
def div (numer denom : Array Digit) : Array Digit × Array Digit :=
  let lnum := numer.size
  let lden := denom.size
  if lnum < lden then
    (Array.replicate (lnum + 1 - lden) 0, (Array.range lden).map fun i => numer.getD i 0)
  else if lnum = 1 && lden = 1 then
    (#[numer.getD 0 0 / denom.getD 0 0], #[numer.getD 0 0 % denom.getD 0 0])
  else if lnum = lden && numer.getD (lnum-1) 0 < denom.getD (lden-1) 0 then
    (Array.replicate (lnum - lden + 1) 0, (Array.range lden).map fun i => numer.getD i 0)
  else
    let (d, u, v) := divNormalize numer denom
    let (u, q) := if lden = 1 then div1 u (v.getD 0 0) else divN u v
    let quot := copyInto (Array.replicate (lnum - lden + 1) 0) q 0 (min q.size (lnum - lden + 1))
    (quot, divUnnormalize u lden d)

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

/-! ## Correctness of `div_1` -/

private theorem lo_of_lt (x : DoubleDigit) (h : x.toNat < base) : (lo x).toNat = x.toNat := by
  have hla := lo_add_hi x
  have hl : (lo x).toNat < base := (lo x).toNat_lt_size
  rcases Nat.eq_zero_or_pos (hi x).toNat with h0 | h0
  · rw [h0, Nat.zero_mul, Nat.add_zero] at hla; exact hla
  · exact absurd hla (by have : base ≤ (hi x).toNat * base := Nat.le_mul_of_pos_left _ h0; omega)

private theorem hi_of_lt (x : DoubleDigit) (h : x.toNat < base) : hi x = 0 := by
  have hla := lo_add_hi x
  have hlo := lo_of_lt x h
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
    rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, show (32 : UInt64).toNat % 64 = 32 from rfl]
    refine Nat.mod_eq_of_lt ?_
    rw [Nat.shiftLeft_eq]
    calc x.toNat * 2 ^ 32 < 4294967296 * 2 ^ 32 :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos 32)).mpr hx
      _ = 2 ^ 64 := by rfl
  rw [UInt64.toNat_or, hshl, UInt32.toNat_toUInt64,
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
  simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, hms, Nat.not_lt]
  exact Nat.mod_le _ _

/-- Each `div_1` step divides its two-digit window exactly. -/
private theorem div1Step_eq (denom : Digit) (u quot : Array Digit) (j : Nat)
    (hd : 0 < denom.toNat) (hlt : (u.getD (j+1) 0).toNat < denom.toNat) :
    ∃ q r : Digit,
      q.toNat = ((u.getD (j+1) 0).toNat * base + (u.getD j 0).toNat) / denom.toNat ∧
      r.toNat = ((u.getD (j+1) 0).toNat * base + (u.getD j 0).toNat) % denom.toNat ∧
      div1Step denom (u, quot) (j+1) = ((u.set! j r).set! (j+1) 0, quot.set! j q) := by
  obtain ⟨W, hW⟩ : ∃ W : DoubleDigit,
      W = ((u.getD (j+1) 0).toUInt64 <<< 32) ||| (u.getD j 0).toUInt64 := ⟨_, rfl⟩
  have hlow : (u.getD j 0).toNat < base := (u.getD j 0).toNat_lt_size
  have hd64 : 0 < denom.toUInt64.toNat := by rw [UInt32.toNat_toUInt64]; exact hd
  have hdb64 : denom.toUInt64.toNat < base := by
    rw [UInt32.toNat_toUInt64]; exact denom.toNat_lt_size
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
  · simp only [div1Step, Nat.add_sub_cancel, ← hW]
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
    · rw [denoteN, denoteN, ih h, getD_set!_ne c idx n d (by omega)]
      omega
    · have hidxn : idx = n := by omega
      subst hidxn
      rw [denoteN, denoteN, denoteN_set!_of_le c idx d (Nat.le_refl _),
        getD_set!_eq c idx d hidx, hz]
      simp

theorem denote_set!_of_zero (c : Array Digit) (idx : Nat) (d : Digit)
    (hidx : idx < c.size) (hz : c.getD idx 0 = 0) :
    denote (c.set! idx d) = denote c + d.toNat * base ^ idx := by
  rw [denote, Array.size_set!, denote]
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
theorem div1Loop_spec (denom : Digit) (numer : Array Digit) (hd : 0 < denom.toNat) :
    ∀ (j : Nat) (u quot : Array Digit), u.size = numer.size → quot.size = numer.size - 1 →
      j < numer.size →
      (∀ i, i < j → u.getD i 0 = numer.getD i 0) →
      (∀ i, i < j → quot.getD i 0 = 0) →
      (u.getD j 0).toNat < denom.toNat →
      denote quot * denom.toNat + denoteN numer j + (u.getD j 0).toNat * base ^ j
        = denoteN numer numer.size →
      ((div1Loop denom u quot j).1.getD 0 0).toNat < denom.toNat ∧
      (div1Loop denom u quot j).2.size = numer.size - 1 ∧
      denote (div1Loop denom u quot j).2 * denom.toNat
          + ((div1Loop denom u quot j).1.getD 0 0).toNat = denoteN numer numer.size := by
  intro j
  induction j with
  | zero =>
    intro u quot hu hq _ _ _ hrem hval
    refine ⟨hrem, hq, ?_⟩
    show denote quot * denom.toNat + (u.getD 0 0).toNat = denoteN numer numer.size
    simpa [denoteN] using hval
  | succ j ih =>
    intro u quot hu hq hjn hlow hqz hrem hval
    obtain ⟨q, r, hqv, hrv, hstep⟩ := div1Step_eq denom u quot j hd hrem
    have hjq : j < quot.size := by omega
    have hju : j < u.size := by omega
    have hnj : u.getD j 0 = numer.getD j 0 := hlow j (by omega)
    have hset : (u.set! j r).getD j 0 = r := getD_set!_eq u j r hju
    rw [div1Loop, hstep]
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
        rw [← Nat.pow_succ]; exact hval
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
    ((div1 numer denom).1.getD 0 0).toNat < denom.toNat ∧
    (div1 numer denom).2.size = numer.size - 1 ∧
    denote (div1 numer denom).2 * denom.toNat + ((div1 numer denom).1.getD 0 0).toNat
      = denoteN numer numer.size := by
  refine div1Loop_spec denom numer hd (numer.size - 1) numer _ rfl (by simp) (by omega)
    (fun _ _ => rfl) (fun i _ => getD_replicate_zero _ _) htop ?_
  rw [denote_replicate_zero, Nat.zero_mul, Nat.zero_add]
  obtain ⟨m, hm⟩ : ∃ m, numer.size = m + 1 := ⟨numer.size - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel]
  rfl

/-! ## Correctness of step D3 -/

/-- Normalization keeps the trial digit within one of a single digit. -/
private theorem q_le_of_inv {q r vtop u2 : Nat} (hinv : u2 = q * vtop + r)
    (hu2 : u2 ≤ vtop * base + (base - 1)) (hnorm : base ≤ 2 * vtop) : q ≤ base + 1 := by
  rcases Nat.lt_or_ge q (base + 2) with h | h
  · omega
  · exfalso
    have h1 : (base + 2) * vtop ≤ q * vtop := Nat.mul_le_mul_right _ h
    have h2 : (base + 2) * vtop = base * vtop + 2 * vtop := by grind
    have h3 : vtop * base = base * vtop := Nat.mul_comm _ _
    simp only [base] at *
    omega

/-- Step D3's test, read arithmetically. -/
private theorem recheck_test_iff (dn2 nu : Digit) (q r : DoubleDigit)
    (hq : q.toNat ≤ base + 1) (hr : r.toNat < base) :
    ((q >>> 32 != 0 || q * dn2.toUInt64 > ((r <<< 32) + nu.toUInt64)) = true)
      = (base ≤ q.toNat ∨ base * r.toNat + nu.toNat < q.toNat * dn2.toNat) := by
  have hd2 : dn2.toNat < base := dn2.toNat_lt_size
  have hnu : nu.toNat < base := nu.toNat_lt_size
  have hq64 : q.toNat < 2 ^ 64 := q.toNat_lt_size
  have hbase : (base : Nat) = 4294967296 := rfl
  have hshr : (q >>> 32).toNat = q.toNat / 4294967296 := by
    rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
      Nat.shiftRight_eq_div_pow]
  have hmul : (q * dn2.toUInt64).toNat = q.toNat * dn2.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    refine Nat.mod_eq_of_lt ?_
    calc q.toNat * dn2.toNat ≤ (base + 1) * (base - 1) := Nat.mul_le_mul hq (by omega)
      _ < 2 ^ 64 := by simp only [base]; omega
  have hshl : ((r <<< 32) + nu.toUInt64).toNat = base * r.toNat + nu.toNat := by
    have h1 : (r <<< 32).toNat = r.toNat * 4294967296 := by
      rw [UInt64.toNat_shiftLeft, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq]
      refine Nat.mod_eq_of_lt ?_
      simp only [base] at hr; omega
    rw [UInt64.toNat_add, h1, UInt32.toNat_toUInt64,
      Nat.mod_eq_of_lt (by simp only [base] at hr hnu ⊢; omega)]
    simp only [base]
    omega
  simp only [bne_iff_ne, ne_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt, hmul, hshl,
    Bool.or_eq_true, decide_eq_true_eq]
  have hz : (¬ (q >>> 32 = 0)) = (base ≤ q.toNat) := by
    rw [eq_iff_iff]
    constructor
    · intro h
      have : (q >>> 32).toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by rw [h0]; rfl))
      rw [hshr] at this
      simp only [base]; omega
    · intro h h0
      have : (q >>> 32).toNat = 0 := by rw [h0]; rfl
      rw [hshr] at this
      simp only [base] at h; omega
  rw [hz]

private theorem shr32_lt (x : DoubleDigit) : ((x >>> 32 == 0) = true) = (x.toNat < base) := by
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt_size
  have hshr : (x >>> 32).toNat = x.toNat / 4294967296 := by
    rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
      Nat.shiftRight_eq_div_pow]
  rw [eq_iff_iff]
  simp only [beq_iff_eq]
  constructor
  · intro h
    have : (x >>> 32).toNat = 0 := by rw [h]; rfl
    rw [hshr] at this
    simp only [base]; omega
  · intro h
    refine UInt64.toNat_inj.mp ?_
    rw [hshr]
    simp only [base] at h
    have : x.toNat / 4294967296 = 0 := by omega
    rw [this]; rfl

private theorem toNat_pred {q : DoubleDigit} (h : 0 < q.toNat) :
    (q - 1).toNat = q.toNat - 1 := by
  have h2 : q.toNat < 2 ^ 64 := q.toNat_lt_size
  rw [UInt64.toNat_sub, show (1 : UInt64).toNat = 1 from rfl]
  omega

private theorem toNat_add_digit (r : DoubleDigit) (d : Digit) (hr : r.toNat < base) :
    (r + d.toUInt64).toNat = r.toNat + d.toNat := by
  have hd : d.toNat < base := d.toNat_lt_size
  simp only [base] at hr hd
  rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
  exact Nat.mod_eq_of_lt (by omega)

set_option maxHeartbeats 400000 in
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
  have hvtop1 : 1 ≤ dn1.toNat := by simp only [base] at hnorm; omega
  have hd2 : dn2.toNat < base := dn2.toNat_lt_size
  have hpow : 0 < base ^ k := Nat.pow_pos (by simp [base])
  have hVpos : 0 < V := by
    rw [hV]
    have h1 : 1 * base ^ k ≤ (dn1.toNat * base + dn2.toNat) * base ^ k :=
      Nat.mul_le_mul_right _ (by simp only [base] at hvtop1 ⊢; omega)
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
    have hf1 : q.toNat < base := by
      rcases Nat.lt_or_ge q.toNat base with h | h
      · exact h
      · exact absurd (Or.inl h) harith
    have hf2 : q.toNat * dn2.toNat ≤ base * r.toNat + nu.toNat := by
      rcases Nat.lt_or_ge (base * r.toNat + nu.toNat) (q.toNat * dn2.toNat) with h | h
      · exact absurd (Or.inr h) harith
      · exact h
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
      rw [hqn, hrn, hm, Nat.add_sub_cancel]
      rw [hm] at hinv
      grind
    have hqsmall : (q - 1).toNat < base := by
      refine Nat.lt_of_mul_lt_mul_right (a := dn1.toNat) ?_
      simp only [base] at hu2 hrbig hinv' ⊢; omega
    refine ⟨hqsmall, by rw [hqn]; exact Nat.le_pred_of_lt hdec, ?_⟩
    refine KnuthD.le_succ_div_of_not_test hV hVpos hU hinv' hvrest hvtop1 hqsmall ?_
    calc (q - 1).toNat * dn2.toNat ≤ (base - 1) * (base - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ base * (r + dn1.toUInt64).toNat := by
          have h1 : base * base ≤ base * (r + dn1.toUInt64).toNat := Nat.mul_le_mul_left _ hrbig
          simp only [base] at h1 ⊢; omega
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
      · have hq0 : q.toNat = 0 := Nat.le_zero.mp hqn
        exact absurd (fires q r hinv hr hfire) (by rw [hq0]; exact Nat.not_lt_zero _)
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
          simp only [hfire, hr2, ite_true]
          refine ih (q - 1) (r + dn1.toUInt64)
            (by rw [hqp]
                exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.sub_lt hqpos Nat.one_pos) hqn))
            ?_ hrlt (by rw [hqp]; exact Nat.le_pred_of_lt hdec)
          obtain ⟨m, hm⟩ : ∃ m, q.toNat = m + 1 :=
            ⟨q.toNat - 1, (Nat.succ_pred_eq_of_pos hqpos).symm⟩
          rw [hqp, hrn, hm, Nat.add_sub_cancel]
          rw [hm] at hinv
          grind
        · have hrbig : base ≤ (r + dn1.toUInt64).toNat := by
            rcases Nat.lt_or_ge (r + dn1.toUInt64).toNat base with h | h
            · exact absurd (shr32_lt (r + dn1.toUInt64) ▸ h) hr2
            · exact h
          rw [recheck.eq_def]
          simp [hfire, Bool.eq_false_iff.mpr hr2]
          exact exitBig q r hinv hr hdec hrbig
      · rw [recheck.eq_def]
        simp [Bool.eq_false_iff.mpr hfire]
        exact exitFail q r hinv hr hle hfire
  intro q r h1 h2 h3
  exact main q.toNat q r (Nat.le_refl _) h1 h2 h3

/-! ## Slices -/

theorem getD_extract (a : Array Digit) (j k i : Nat) (h : i < k - j) (hk : k ≤ a.size) :
    (a.extract j k).getD i 0 = a.getD (j+i) 0 := by
  have h1 : i < (a.extract j k).size := by simp; omega
  have h2 : j + i < a.size := by omega
  simp [h2, Nat.min_eq_left hk, h]

theorem denote_extract_zero (a : Array Digit) (j : Nat) : denote (a.extract j j) = 0 := by
  rw [denote]
  have : (a.extract j j).size = 0 := by simp; omega
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
      have hsz : (a.extract j (k+1)).size = k + 1 - j := by simp; omega
      have hpush : denote (a.extract j (k+1))
          = denote (a.extract j k) + (a.getD k 0).toNat * base ^ (k - j) := by
        have hsz' : (a.extract j k).size = k - j := by simp; omega
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
      rw [denoteN, ih hjk' (by omega), hpush, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add,
        show k - j + j = k by omega]
      omega

/-! ## Bulk digit copies -/

theorem size_copyInto (dst src : Array Digit) (j len : Nat) :
    (copyInto dst src j len).size = dst.size := by
  induction len with
  | zero => rfl
  | succ len ih => rw [copyInto, Array.size_set!, ih]

theorem getD_copyInto_of_lt (dst src : Array Digit) (j len i : Nat) (h : i < j) :
    (copyInto dst src j len).getD i 0 = dst.getD i 0 := by
  induction len with
  | zero => rfl
  | succ len ih => rw [copyInto, getD_set!_ne _ _ _ _ (by omega), ih]

theorem getD_copyInto_of_ge (dst src : Array Digit) (j len i : Nat) (h : j + len ≤ i) :
    (copyInto dst src j len).getD i 0 = dst.getD i 0 := by
  induction len with
  | zero => rfl
  | succ len ih => rw [copyInto, getD_set!_ne _ _ _ _ (by omega), ih (by omega)]

theorem denoteN_copyInto (dst src : Array Digit) (j : Nat) :
    ∀ len, j + len ≤ dst.size →
      denoteN (copyInto dst src j len) (j + len) = denoteN dst j + denoteN src len * base ^ j := by
  intro len
  induction len with
  | zero => intro _; simp [copyInto, denoteN]
  | succ len ih =>
    intro h
    have hsz : (copyInto dst src j len).size = dst.size := size_copyInto ..
    rw [show j + (len+1) = (j + len) + 1 by omega, copyInto,
      denoteN_set!_succ _ _ _ (by rw [hsz]; omega), ih (by omega), denoteN,
      Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, show len + j = j + len by omega]
    omega

theorem getD_copyInto_mid (dst src : Array Digit) (j : Nat) :
    ∀ len i, j ≤ i → i < j + len → j + len ≤ dst.size →
      (copyInto dst src j len).getD i 0 = src.getD (i - j) 0 := by
  intro len
  induction len with
  | zero => intro i _ h _; omega
  | succ len ih =>
    intro i h1 h2 h3
    rcases Nat.lt_or_ge i (j + len) with h | h
    · rw [copyInto, getD_set!_ne _ _ _ _ (by omega)]
      exact ih i h1 h (by omega)
    · have hi : i = j + len := by omega
      subst hi
      rw [copyInto, getD_set!_eq _ _ _ (by rw [size_copyInto]; omega)]
      congr 1
      omega

/-- After a copy, the window at `j` reads back exactly the digits that were written. -/
theorem denote_extract_copyInto (dst src : Array Digit) (j len : Nat)
    (hsz : j + len ≤ dst.size) :
    denote ((copyInto dst src j len).extract j (j + len)) = denoteN src len := by
  have hcsz : (copyInto dst src j len).size = dst.size := size_copyInto ..
  have hesz : ((copyInto dst src j len).extract j (j + len)).size = len := by
    simp [hcsz]; omega
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
      rw [denoteN, hK, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add,
        show n - m + m = n by omega]
      omega

/-- Reading only the first `m` digits is truncation to `base ^ m`. -/
theorem denoteN_mod (a : Array Digit) (m : Nat) : denoteN a m = denote a % base ^ m := by
  rcases Nat.lt_or_ge m a.size with h | h
  · obtain ⟨K, hK⟩ := denoteN_add_high a m a.size (by omega)
    rw [denote, hK, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (denoteN_lt a m)]
  · rw [denoteN_of_ge a h, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le (denoteN_lt a a.size)
      (Nat.pow_le_pow_right (by simp [base]) h)

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
    denote (u.extract j (j+k+3)) / denote denom ≤ (divNTrial denom u j).toNat ∧
    (divNTrial denom u j).toNat ≤ denote (u.extract j (j+k+3)) / denote denom + 1 := by
  have hvtop1 : 1 ≤ (denom.getD (k+1) 0).toNat := by simp only [base] at hnorm; omega
  have hpk : 0 < base ^ k := Nat.pow_pos (by simp [base])
  have hpk1 : 0 < base ^ (k+1) := Nat.pow_pos (by simp [base])
  -- the divisor, split at its top two digits
  have hV : denote denom
      = ((denom.getD (k+1) 0).toNat * base + (denom.getD k 0).toNat) * base ^ k + denoteN denom k := by
    rw [denote, hk]; exact denoteN_split_two denom k
  have hvrest : denoteN denom k < base ^ k := denoteN_lt denom k
  -- the window, split in the shape step D3 reads it
  have hWsz : (u.extract j (j+k+3)).size = k + 3 := by simp; omega
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
        Nat.mul_le_mul_right _ (by simp only [base] at hd2 ⊢; omega)
      have h2 : (base - 1) * base ^ k + base ^ k = base ^ (k+1) := by
        rw [Nat.pow_succ]; simp only [base]; grind
      omega
    have h3 : ((denom.getD (k+1) 0).toNat + 1) * base ^ (k+1)
        = (denom.getD (k+1) 0).toNat * base * base ^ k + base ^ (k+1) := by
      rw [Nat.pow_succ, Nat.add_mul, Nat.one_mul]; grind
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
            (Nat.mul_lt_mul_right (by simp [base])).mpr hVlt
        _ = (((denom.getD (k+1) 0).toNat + 1) * base) * base ^ (k+1) := by grind
    have := Nat.lt_of_mul_lt_mul_right (a := base ^ (k+1)) (Nat.lt_of_le_of_lt hge hlt)
    simp only [base] at this ⊢; omega
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
        rw [Nat.pow_succ]; grind
      have h2 : (denom.getD k 0).toNat * base ^ k + denoteN denom k < base ^ (k+1) := by
        have hd2 : (denom.getD k 0).toNat < base := (denom.getD k 0).toNat_lt_size
        have ha : (denom.getD k 0).toNat * base ^ k ≤ (base - 1) * base ^ k :=
          Nat.mul_le_mul_right _ (by simp only [base] at hd2 ⊢; omega)
        have hb : (base - 1) * base ^ k + base ^ k = base ^ (k+1) := by
          rw [Nat.pow_succ]; simp only [base]; grind
        omega
      rw [h1, Nat.mul_comm, Nat.mul_add_div hpk1, Nat.div_eq_of_lt h2, Nat.add_zero]
    have hUd : denote (u.extract j (j+k+3)) / base ^ (k+1)
        = (u.getD (j+k+2) 0).toNat * base + (u.getD (j+k+1) 0).toNat := by
      rw [hU]
      have h2 : (u.getD (j+k) 0).toNat * base ^ k + denoteN (u.extract j (j+k+3)) k
          < base ^ (k+1) := by
        have hd3 : (u.getD (j+k) 0).toNat < base := (u.getD (j+k) 0).toNat_lt_size
        have ha : (u.getD (j+k) 0).toNat * base ^ k ≤ (base - 1) * base ^ k :=
          Nat.mul_le_mul_right _ (by simp only [base] at hd3 ⊢; omega)
        have hb : (base - 1) * base ^ k + base ^ k = base ^ (k+1) := by
          rw [Nat.pow_succ]; simp only [base]; grind
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
  have hdt : divNTrial denom u j
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
  have h2 : q.toNat < 2 ^ 32 := q.toNat_lt_size
  rw [UInt32.toNat_sub, show (1 : UInt32).toNat = 1 from rfl]
  omega

set_option maxHeartbeats 1000000 in
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
    (divNStep denom (u, quot) j).1.size = u.size ∧
    (divNStep denom (u, quot) j).2.size = m ∧
    (∀ i, j + denom.size ≤ i → (divNStep denom (u, quot) j).1.getD i 0 = 0) ∧
    (∀ i, i ≠ j → (divNStep denom (u, quot) j).2.getD i 0 = quot.getD i 0) ∧
    denote (divNStep denom (u, quot) j).1 < denote denom * base ^ j ∧
    denote (divNStep denom (u, quot) j).2 * denote denom
        + denote (divNStep denom (u, quot) j).1
      = denote quot * denote denom + denote u := by
  have hjs : j + denom.size + 1 = j + k + 3 := by omega
  have hsz3 : j + k + 3 ≤ u.size := by omega
  have hvtop1 : 1 ≤ (denom.getD (k+1) 0).toNat := by simp only [base] at hnorm; omega
  have hpj : 0 < base ^ j := Nat.pow_pos (by simp [base])
  have hpk : 0 < base ^ k := Nat.pow_pos (by simp [base])
  have hVlt : denote denom < base ^ (k+2) := by
    have h := denoteN_lt denom denom.size
    rw [← denote, hk] at h; exact h
  have hVpos : 0 < denote denom := by
    have hsplit : denote denom
        = ((denom.getD (k+1) 0).toNat * base + (denom.getD k 0).toNat) * base ^ k
          + denoteN denom k := by rw [denote, hk]; exact denoteN_split_two denom k
    have h1 : 1 * base ^ k
        ≤ ((denom.getD (k+1) 0).toNat * base + (denom.getD k 0).toNat) * base ^ k :=
      Nat.mul_le_mul_right _ (by simp only [base] at hvtop1 ⊢; omega)
    omega
  -- the window, and its bound
  have hwin_eq : denote u = denoteN u j + denote (u.extract j (j+k+3)) * base ^ j := by
    rw [denote_of_high_zero u (n := j+k+3) (by omega) (fun i hi => hhigh i (by omega))]
    exact denoteN_extract u (j+k+3) (by omega) (by omega)
  have hW : denote (u.extract j (j+k+3)) < denote denom * base := by
    have h1 : denote (u.extract j (j+k+3)) * base ^ j ≤ denote u := by rw [hwin_eq]; omega
    have h2 : denote denom * base ^ (j+1) = denote denom * base * base ^ j := by
      rw [Nat.pow_succ]; grind
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt h1 (h2 ▸ hbound))
  obtain ⟨hq1, hq2⟩ := divNTrial_spec denom u j k hk hnorm hsz3 hW
  -- name the pieces of the step
  obtain ⟨q, hq⟩ : ∃ x, x = divNTrial denom u j := ⟨_, rfl⟩
  obtain ⟨ms, hms⟩ : ∃ x, x = mul #[q] denom := ⟨_, rfl⟩
  obtain ⟨dw, hdw⟩ : ∃ x, x = sub (u.extract j (j + denom.size + 1)) ms := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ x, x = copyInto u dw.1 j (denom.size + 1) := ⟨_, rfl⟩
  rw [← hq] at hq1 hq2
  have hstep : divNStep denom (u, quot) j =
      if dw.2 != 0 then
        (copyInto u1 (add denom (u1.extract j (j + denom.size + 1))) j (denom.size + 1),
         quot.set! j (q - 1))
      else (u1, quot.set! j q) := by
    simp only [divNStep, ← hq, ← hms, ← hdw, ← hu1]
  -- the subtraction
  have hmssz : ms.size = 1 + denom.size := by rw [hms]; exact size_mul ..
  have hmsval : denote ms = q.toNat * denote denom := by
    rw [hms, denote_mul, denote_singleton]
  have hextsz : (u.extract j (j + denom.size + 1)).size = denom.size + 1 := by
    simp; omega
  have hmax : max (u.extract j (j + denom.size + 1)).size ms.size = denom.size + 1 := by
    rw [hextsz, hmssz]; omega
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
    have hu'sz0 : j + denom.size + 1 ≤ u'.size := by rw [hsz', husz]; omega
    have hextsz' : (u'.extract j (j + denom.size + 1)).size = denom.size + 1 := by
      simp; omega
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
          rw [hsplit]; omega
        rw [hwin'] at hge
        omega
    have hzero : ∀ i, j + denom.size ≤ i → u'.getD i 0 = 0 := by
      intro i hi
      rcases Nat.eq_or_lt_of_le hi with h | h
      · rw [← h]; exact htop
      · rw [hhigh' i (by omega)]; exact hhigh i (by omega)
    have hden' : denote u' = denoteN u j + (denote (u.extract j (j+k+3)) % denote denom) * base ^ j := by
      have hu'sz : j + denom.size + 1 ≤ u'.size := by rw [hsz', husz]; omega
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
  have hmodlt : denote (u.extract j (j+k+3)) % denote denom < denote denom := Nat.mod_lt _ hVpos
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
      rw [hqeq]; grind
    have habv : denote (add denom (u1.extract j (j + denom.size + 1)))
        = denote (u.extract j (j+k+3)) % denote denom + base ^ (denom.size + 1) := by
      rw [denote_add, hu1win]
      omega
    have hsmall : denote (u.extract j (j+k+3)) % denote denom < base ^ (denom.size + 1) := by
      have : base ^ (k+2) ≤ base ^ (denom.size + 1) :=
        Nat.pow_le_pow_right (by simp [base]) (by omega)
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
      rw [hqeq] at hdwval; omega
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
      (divNLoop denom u quot p).1.size = m + denom.size ∧
      (divNLoop denom u quot p).2.size = m ∧
      denote (divNLoop denom u quot p).1 < denote denom ∧
      denote (divNLoop denom u quot p).2 * denote denom + denote (divNLoop denom u quot p).1
        = denote quot * denote denom + denote u := by
  intro p
  induction p with
  | zero =>
    intro u quot _ husz hqsz _ _ hbound
    refine ⟨husz, hqsz, ?_, rfl⟩
    show denote u < denote denom
    simpa using hbound
  | succ p ih =>
    intro u quot hp husz hqsz hhigh hqz hbound
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := divNStep_spec denom u quot p k m hk hnorm husz hqsz
      (by omega) (hqz p (by omega)) hhigh hbound
    rw [divNLoop]
    obtain ⟨g1, g2, g3, g4⟩ := ih (divNStep denom (u, quot) p).1 (divNStep denom (u, quot) p).2
      (by omega) (by rw [h1, husz]) h2 h3
      (fun i hi => by rw [h4 i (by omega)]; exact hqz i (by omega)) h5
    exact ⟨g1, g2, g3, by rw [g4, h6]⟩

/-- `div_n` divides: quotient times divisor plus remainder is the numerator. -/
theorem divN_spec (numer denom : Array Digit) (k : Nat)
    (hk : denom.size = k + 2)
    (hnorm : base ≤ 2 * (denom.getD (k+1) 0).toNat)
    (hsz : denom.size ≤ numer.size)
    (hbound : denote numer < denote denom * base ^ (numer.size - denom.size)) :
    (divN numer denom).1.size = numer.size ∧
    (divN numer denom).2.size = numer.size - denom.size ∧
    denote (divN numer denom).1 < denote denom ∧
    denote (divN numer denom).2 * denote denom + denote (divN numer denom).1 = denote numer := by
  obtain ⟨g1, g2, g3, g4⟩ := divNLoop_spec denom k (numer.size - denom.size) hk hnorm
    (numer.size - denom.size) numer (Array.replicate (numer.size - denom.size) 0)
    (Nat.le_refl _) (by omega) (by simp) (fun i hi => getD_of_ge numer (by omega))
    (fun i _ => getD_replicate_zero _ _) hbound
  rw [divN]
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
  have hbt : b.size = t + 1 := by rw [← hs, ht]
  have hta : a.size - 1 = t := by omega
  have htb : b.size - 1 = t := by omega
  rw [hta, htb] at h
  have ha : denote a = denoteN a t + (a.getD t 0).toNat * base ^ t := by rw [denote, ht]; rfl
  have hb : denote b = denoteN b t + (b.getD t 0).toNat * base ^ t := by rw [denote, hbt]; rfl
  have h1 : denoteN a t < base ^ t := denoteN_lt a t
  have h3 : ((a.getD t 0).toNat + 1) * base ^ t ≤ (b.getD t 0).toNat * base ^ t :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : ((a.getD t 0).toNat + 1) * base ^ t = (a.getD t 0).toNat * base ^ t + base ^ t := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

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

/-- Both operands scaled by the same amount: same quotient, remainder scaled. -/
private theorem div_mod_scaled (N D t : Nat) (ht : 0 < t) :
    (N * t) / (D * t) = N / D ∧ (N * t) % (D * t) = (N % D) * t :=
  ⟨Nat.mul_div_mul_right _ _ ht, Nat.mul_mod_mul_right ..⟩

set_option maxHeartbeats 1000000 in
/--
`mpn_div` divides: what it returns are the quotient and remainder of the
operands. The preconditions are the ones every in-tree caller satisfies, since
`mpz` keeps its sizes normalized and `lean_nat_div` rejects a zero divisor.
-/
theorem div_spec (numer denom : Array Digit)
    (hden : 0 < denom.size) (hsz : denom.size ≤ numer.size)
    (htop : 0 < (denom.getD (denom.size - 1) 0).toNat) :
    denote (div numer denom).1 = denote numer / denote denom ∧
    denote (div numer denom).2 = denote numer % denote denom := by
  have hnum : 0 < numer.size := by omega
  have hVpos : 0 < denote denom := by
    obtain ⟨t, ht⟩ : ∃ t, denom.size = t + 1 := ⟨denom.size - 1, by omega⟩
    have hd : denote denom = denoteN denom t + (denom.getD t 0).toNat * base ^ t := by
      rw [denote, ht]; rfl
    have ht1 : denom.size - 1 = t := by omega
    rw [ht1] at htop
    have h1 : 1 * base ^ t ≤ (denom.getD t 0).toNat * base ^ t :=
      Nat.mul_le_mul_right _ (by omega)
    have hp : 0 < base ^ t := Nat.pow_pos (by simp [base])
    omega
  rw [div]
  simp only [show ¬ (numer.size < denom.size) from by omega, ite_false]
  by_cases hB : (numer.size = 1 && denom.size = 1) = true
  · -- both single digit: the hardware divide
    simp only [hB, ite_true]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    have hN : denote numer = (numer.getD 0 0).toNat := by rw [denote, hB.1]; simp [denoteN]
    have hD : denote denom = (denom.getD 0 0).toNat := by rw [denote, hB.2]; simp [denoteN]
    exact ⟨by rw [denote_singleton, UInt32.toNat_div, hN, hD],
      by rw [denote_singleton, UInt32.toNat_mod, hN, hD]⟩
  · simp only [Bool.eq_false_iff.mpr hB, Bool.false_eq_true, ite_false]
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
      obtain ⟨hd32, husz, hvsz, huval, hvval, hvnorm⟩ :=
        divNormalize_spec numer denom hnum hden htop
      rw [hduv] at hd32 husz hvsz huval hvval hvnorm ⊢
      dsimp only at hd32 husz hvsz huval hvval hvnorm ⊢
      have h2d : 0 < 2 ^ dd := Nat.pow_pos (by omega)
      have hdle : (2:Nat) ^ dd ≤ 2147483648 := by
        simp only [digitBits] at hd32
        calc (2:Nat) ^ dd ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) (by omega)
          _ = 2147483648 := by rfl
      have hVpos' : 0 < denote v := by rw [hvval]; exact Nat.mul_pos hVpos h2d
      have hNlt : denote numer < base ^ numer.size := denoteN_lt numer numer.size
      -- the divisor's leading digit, and what it forces about `u`'s
      have hvsplit : denote v = denoteN v (denom.size - 1)
          + (v.getD (denom.size - 1) 0).toNat * base ^ (denom.size - 1) := by
        obtain ⟨t, ht⟩ : ∃ t, denom.size = t + 1 := ⟨denom.size - 1, by omega⟩
        have ht1 : denom.size - 1 = t := by omega
        rw [ht1, denote, hvsz, ht]; rfl
      have husplit : denote u = denoteN u numer.size
          + (u.getD numer.size 0).toNat * base ^ numer.size := by
        rw [denote, husz]; rfl
      have hutop : (u.getD numer.size 0).toNat < 2 ^ dd := by
        have h1 : denoteN u numer.size < base ^ numer.size := denoteN_lt u numer.size
        have h2 : denote u < 2 ^ dd * base ^ numer.size := by
          rw [huval, Nat.mul_comm]
          exact (Nat.mul_lt_mul_left h2d).mpr hNlt
        exact Nat.lt_of_mul_lt_mul_right (a := base ^ numer.size) (by omega)
      -- run the inner division
      obtain ⟨u', q, hres⟩ : ∃ u' q,
          (if denom.size = 1 then div1 u (v.getD 0 0) else divN u v) = (u', q) := ⟨_, _, rfl⟩
      have hmain : q.size = numer.size - denom.size + 1 ∧
          denote q = denote u / denote v ∧
          denoteN u' denom.size = denote u % denote v := by
        by_cases h1 : denom.size = 1
        · rw [show (if denom.size = 1 then div1 u (v.getD 0 0) else divN u v)
              = div1 u (v.getD 0 0) from by simp [h1]] at hres
          have hv0 : 2147483648 ≤ (v.getD 0 0).toNat := by
            have he : denom.size - 1 = 0 := by omega
            rw [he] at hvnorm; exact hvnorm
          have hvd : 0 < (v.getD 0 0).toNat := by omega
          have hvdD : denote v = (v.getD 0 0).toNat := by rw [denote, hvsz, h1]; simp [denoteN]
          obtain ⟨g1, g2, g3⟩ := div1_spec u (v.getD 0 0) hvd (by omega)
            (by have hh : u.size - 1 = numer.size := by omega
                rw [hh]; omega)
          rw [hres] at g1 g2 g3
          dsimp only at g1 g2 g3
          rw [← denote] at g3
          obtain ⟨e1, e2⟩ := div_mod_of_eq (V := (v.getD 0 0).toNat) hvd g3 g1
          rw [← hvdD] at e1 e2
          refine ⟨by rw [g2, husz, h1]; omega, e1, ?_⟩
          rw [h1, denoteN, denoteN, ← e2]; simp
        · rw [show (if denom.size = 1 then div1 u (v.getD 0 0) else divN u v)
              = divN u v from by simp [h1]] at hres
          have hk : denom.size = (denom.size - 2) + 2 := by omega
          have hvk : v.size = (denom.size - 2) + 2 := by rw [hvsz]; omega
          have hidx : denom.size - 2 + 1 = denom.size - 1 := by omega
          have hnorm2 : base ≤ 2 * (v.getD (denom.size - 2 + 1) 0).toNat := by
            rw [hidx]; simp only [base]; omega
          have hbnd : denote u < denote v * base ^ (u.size - v.size) := by
            have hb1 : (v.getD (denom.size - 1) 0).toNat * base ^ (denom.size - 1) ≤ denote v := by
              omega
            have hb2 : 2147483648 * base ^ (denom.size - 1) ≤ denote v :=
              Nat.le_trans (Nat.mul_le_mul_right _ hvnorm) hb1
            have hb3 : denote v * base ^ (u.size - v.size)
                ≥ 2147483648 * base ^ (denom.size - 1) * base ^ (u.size - v.size) :=
              Nat.mul_le_mul_right _ hb2
            have hb4 : base ^ (denom.size - 1) * base ^ (u.size - v.size) = base ^ numer.size := by
              rw [← Nat.pow_add]; congr 1; rw [husz, hvsz]; omega
            have hb5 : denote u < 2147483648 * base ^ numer.size := by
              rw [huval]
              calc denote numer * 2 ^ dd ≤ denote numer * 2147483648 :=
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
                Nat.pow_le_pow_right (by simp [base]) hi
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

/-! ## Correctness of `mpn_compare` -/

/-- A bigger leading digit outweighs everything below it. -/
private theorem denoteN_lt_of_digit_lt (a b : Array Digit) (n : Nat)
    (h : (a.getD n 0).toNat < (b.getD n 0).toNat) : denoteN a (n+1) < denoteN b (n+1) := by
  have h1 : denoteN a n < base ^ n := denoteN_lt a n
  have h2 : ((a.getD n 0).toNat + 1) * base ^ n ≤ (b.getD n 0).toNat * base ^ n :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : ((a.getD n 0).toNat + 1) * base ^ n
      = (a.getD n 0).toNat * base ^ n + base ^ n := by rw [Nat.add_mul, Nat.one_mul]
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
    have hgt : (a.getD n 0 > b.getD n 0) = ((b.getD n 0).toNat < (a.getD n 0).toNat) := by
      simp [UInt32.lt_iff_toNat_lt]
    have hlt : (a.getD n 0 < b.getD n 0) = ((a.getD n 0).toNat < (b.getD n 0).toNat) := by
      simp [UInt32.lt_iff_toNat_lt]
    rw [compareLoop]
    simp only [hgt, hlt]
    rcases Nat.lt_trichotomy (a.getD n 0).toNat (b.getD n 0).toNat with h | h | h
    · have hd := denoteN_lt_of_digit_lt a b n h
      simp only [show ((b.getD n 0).toNat < (a.getD n 0).toNat) = False from eq_false (by omega),
        show ((a.getD n 0).toNat < (b.getD n 0).toNat) = True from eq_true h,
        show (denoteN b (n+1) < denoteN a (n+1)) = False from eq_false (by omega),
        show (denoteN a (n+1) < denoteN b (n+1)) = True from eq_true hd, ite_true, ite_false]
    · have hdeq : a.getD n 0 = b.getD n 0 := UInt32.toNat_inj.mp h
      simp only [ih, denoteN, hdeq]
      simp
    · have hd := denoteN_lt_of_digit_lt b a n h
      simp only [show ((b.getD n 0).toNat < (a.getD n 0).toNat) = True from eq_true h,
        show (denoteN b (n+1) < denoteN a (n+1)) = True from eq_true hd, ite_true]

/-- `mpn_compare` reports the order of its operands. -/
theorem compare_spec (a b : Array Digit) :
    compare a b = if denote b < denote a then 1 else if denote a < denote b then -1 else 0 := by
  rw [compare, compareLoop_spec, denoteN_of_ge a (Nat.le_max_left ..),
    denoteN_of_ge b (Nat.le_max_right ..)]

/-!
## The `mpz` layer

Every `mpn` specification above takes its preconditions as hypotheses: a
nonempty digit array, a divisor no longer than the dividend, a nonzero leading
divisor digit. `mpz` is what establishes them, by keeping every value in a
normalized shape and by sizing the buffers it hands to `mpn`. Bundling that
shape into a type discharges the preconditions once, structurally, instead of
assuming them at each use.
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
  unfold trim
  split <;> rename_i hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact size_trim_pos c.pop (by simp; omega)
  · exact h
termination_by c.size
decreasing_by simp_all; omega

theorem trim_top_ne_zero (c : Array Digit) :
    1 < (trim c).size → ((trim c).getD ((trim c).size - 1) 0).toNat ≠ 0 := by
  unfold trim
  split <;> rename_i hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact trim_top_ne_zero c.pop
  · intro hgt he
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hc
    exact hc hgt (UInt32.toNat_inj.mp (by rw [he]; rfl))
termination_by c.size
decreasing_by simp_all; omega

/-- `mpz::set`: drop leading zero digits, keeping at least one. -/
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
  rw [show a.digits.size - 1 = t from by omega]
  omega

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
        Nat.pow_le_pow_right (by simp [base]) (by omega)
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
    rw [hsz]
    simp only [Nat.sub_self]
    omega
theorem size_add_pos (a b : Array Digit) : 0 < (Mpn.add a b).size := by
  rw [add]; exact size_trim_pos _ (by simp)

theorem size_div_quot (numer denom : Array Digit) (hden : 0 < denom.size)
    (hsz : denom.size ≤ numer.size) :
    (div numer denom).1.size = numer.size - denom.size + 1 := by
  rw [div]
  simp only [show ¬ (numer.size < denom.size) from by omega, ite_false]
  split <;> rename_i hB
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    simp [hB.1, hB.2]
  · split <;> rename_i hC
    · simp
    · simp [size_copyInto]

theorem size_div_rem (numer denom : Array Digit) (hden : 0 < denom.size)
    (hsz : denom.size ≤ numer.size) : (div numer denom).2.size = denom.size := by
  rw [div]
  simp only [show ¬ (numer.size < denom.size) from by omega, ite_false]
  split <;> rename_i hB
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    simp [hB.2]
  · split <;> rename_i hC
    · simp
    · simp [divUnnormalize, size_shiftRightDigits]

/-! ### The operations `mpz` builds on `mpn` -/

/-- `mpn_compare` lifted to normalized values. -/
def Num.compare (a b : Num) : Int := Mpn.compare a.digits b.digits

theorem Num.compare_spec (a b : Num) :
    a.compare b = if b.val < a.val then 1 else if a.val < b.val then -1 else 0 :=
  Mpn.compare_spec a.digits b.digits

/-- `mpz::operator+=` on non-negative values: `mpn_add`, then normalize. -/
def Num.add (a b : Num) : Num := Num.ofArray (Mpn.add a.digits b.digits) (size_add_pos ..)

@[simp] theorem Num.val_add (a b : Num) : (a.add b).val = a.val + b.val := by
  rw [Num.add, Num.val_ofArray, denote_add, Num.val, Num.val]

/-- `mpz::operator*=`: `mpn_mul`, then normalize. -/
def Num.mul (a b : Num) : Num :=
  Num.ofArray (Mpn.mul a.digits b.digits) (by rw [size_mul]; have := a.size_pos; omega)

@[simp] theorem Num.val_mul (a b : Num) : (a.mul b).val = a.val * b.val := by
  rw [Num.mul, Num.val_ofArray, denote_mul, Num.val, Num.val]

/--
`Nat.sub` at the `mpz` layer: compare, and either return zero, as
`lean_nat_big_sub` does when the difference would be negative, or subtract and
normalize.
-/
def Num.sub (a b : Num) : Num :=
  if Mpn.compare a.digits b.digits ≤ 0 then ⟨#[0], by simp, by simp⟩
  else Num.ofArray (Mpn.sub a.digits b.digits).1 (by
    rw [size_sub]; have := a.size_pos; omega)

@[simp] theorem Num.val_sub (a b : Num) : (a.sub b).val = a.val - b.val := by
  have hc : Mpn.compare a.digits b.digits
      = if b.val < a.val then 1 else if a.val < b.val then -1 else 0 := Num.compare_spec a b
  rw [Num.sub]
  split <;> rename_i h
  · -- the guard says the difference would be negative, so the result is zero
    have hle : a.val ≤ b.val := by
      rcases Nat.lt_or_ge b.val a.val with hlt | hle
      · exfalso
        have h1 : Mpn.compare a.digits b.digits = 1 := by rw [hc]; simp [hlt]
        omega
      · exact hle
    show denote #[0] = _
    rw [denote_singleton, show ((0 : Digit)).toNat = 0 from rfl]
    omega
  · have hlt : b.val < a.val := by
      rcases Nat.lt_or_ge b.val a.val with hlt | hle
      · exact hlt
      · exfalso
        refine h ?_
        rw [hc]
        rcases Nat.lt_or_ge a.val b.val with h2 | h2
        · simp [Nat.not_lt.mpr hle, h2]
        · simp [Nat.not_lt.mpr hle, Nat.not_lt.mpr h2]
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
    rw [hb0, Nat.zero_mul, Nat.add_zero] at hd
    rw [Num.val_ofArray]
    simp only [Num.val]
    omega

/-- `mpz::div`: return zero if the divisor is longer, else `mpn_div` and normalize. -/
def Num.div (a b : Num) : Num :=
  if h : a.digits.size < b.digits.size then ⟨#[0], by simp, by simp⟩
  else Num.ofArray (Mpn.div a.digits b.digits).1 (by
    rw [size_div_quot _ _ b.size_pos (by omega)]; omega)

/-- `mpz::rem`: return the dividend if the divisor is longer, else `mpn_div` and normalize. -/
def Num.mod (a b : Num) : Num :=
  if h : a.digits.size < b.digits.size then a
  else Num.ofArray (Mpn.div a.digits b.digits).2 (by
    rw [size_div_rem _ _ b.size_pos (by omega)]; exact b.size_pos)

theorem Num.val_div (a b : Num) (hb : b.val ≠ 0) : (a.div b).val = a.val / b.val := by
  rw [Num.div]
  split <;> rename_i h
  · have hlt : a.val < b.val := by
      rcases Nat.lt_or_ge a.val b.val with h2 | h2
      · exact h2
      · exact absurd (Num.size_le_of_val_le b a h2) (by omega)
    show denote #[0] = _
    rw [denote_singleton, Nat.div_eq_of_lt hlt]
    rfl
  · rw [Num.val_ofArray]
    exact (div_spec a.digits b.digits b.size_pos (by omega) (b.top_pos hb)).1

theorem Num.val_mod (a b : Num) (hb : b.val ≠ 0) : (a.mod b).val = a.val % b.val := by
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

/-- `mpz::is_zero()`. -/
def Num.isZero (a : Num) : Bool := a.digits.size = 1 && a.digits.getD 0 0 == 0

/-- `mul2k`: shift left by `k` bits, then normalize. -/
def Num.shiftLeft (a : Num) (k : Nat) : Num :=
  if k = 0 || a.isZero then a
  else
    Num.ofArray
      (shiftLeftDigits ((Array.replicate (k / digitBits) 0) ++ a.digits)
        (k % digitBits) (a.digits.size + k / digitBits + 1))
      (by rw [size_shiftLeftDigits]; exact Nat.succ_pos _)

/-- `div2k`: shift right by `k` bits, then normalize. -/
def Num.shiftRight (a : Num) (k : Nat) : Num :=
  if k = 0 || a.isZero then a
  else if h : a.digits.size ≤ k / digitBits then ⟨#[0], by simp, by simp⟩
  else
    Num.ofArray
      (shiftRightDigits (a.digits.extract (k / digitBits) a.digits.size)
        (k % digitBits) (a.digits.size - k / digitBits))
      (by rw [size_shiftRightDigits]; omega)

/-- Any digit array as a `Num`, for building test values. -/
def Num.ofArray! (a : Array Digit) : Num :=
  if h : 0 < a.size then Num.ofArray a h else ⟨#[0], by simp, by simp⟩

@[simp] theorem Num.val_ofArray! (a : Array Digit) (h : 0 < a.size) :
    (Num.ofArray! a).val = denote a := by
  unfold Num.ofArray!
  split <;> rename_i h2
  · exact Num.val_ofArray a h2
  · exact absurd h h2
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

theorem Num.val_isZero (a : Num) (h : a.isZero) : a.val = 0 := by
  simp only [Num.isZero, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [Num.val, denote, h.1]
  simp [denoteN, h.2]

/-- `mul2k` shifts left: it multiplies by `2^k`. -/
theorem Num.val_shiftLeft (a : Num) (k : Nat) : (a.shiftLeft k).val = a.val * 2 ^ k := by
  rw [Num.shiftLeft]
  split <;> rename_i h
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [h]; simp
    · rw [Num.val_isZero a h]; simp
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
    have hbit : k % digitBits < digitBits := Nat.mod_lt _ (by simp [digitBits])
    have hpad : denote ((Array.replicate (k / digitBits) (0 : Digit)) ++ a.digits)
        = a.val * base ^ (k / digitBits) := denote_zeros_append a.digits _
    have hfit : denote ((Array.replicate (k / digitBits) (0 : Digit)) ++ a.digits)
        * 2 ^ (k % digitBits) < base ^ (a.digits.size + k / digitBits + 1) := by
      have h1 : a.val < base ^ a.digits.size := a.val_lt
      have h2 : (2:Nat) ^ (k % digitBits) ≤ base := by
        calc (2:Nat) ^ (k % digitBits) ≤ 2 ^ 32 :=
              Nat.pow_le_pow_right (by omega) (by simp only [digitBits] at hbit ⊢; omega)
          _ = base := rfl
      calc denote ((Array.replicate (k / digitBits) (0 : Digit)) ++ a.digits)
            * 2 ^ (k % digitBits)
          = a.val * base ^ (k / digitBits) * 2 ^ (k % digitBits) := by rw [hpad]
        _ < base ^ a.digits.size * base ^ (k / digitBits) * 2 ^ (k % digitBits) := by
            refine (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr ?_
            exact (Nat.mul_lt_mul_right (Nat.pow_pos (by simp [base]))).mpr h1
        _ ≤ base ^ a.digits.size * base ^ (k / digitBits) * base :=
            Nat.mul_le_mul_left _ h2
        _ = base ^ (a.digits.size + k / digitBits + 1) := by
            rw [← Nat.pow_add, ← Nat.pow_succ]
    rw [Num.val_ofArray,
      denote_shiftLeftDigits _ hbit (by simp; omega) hfit, hpad, Nat.mul_assoc,
      base_pow, ← Nat.pow_add]
    congr 2
    simp only [digitBits]
    omega

/-- `div2k` shifts right: it divides by `2^k`. -/
theorem Num.val_shiftRight (a : Num) (k : Nat) : (a.shiftRight k).val = a.val / 2 ^ k := by
  have hbit : k % digitBits < digitBits := Nat.mod_lt _ (by simp [digitBits])
  have hk : 32 * (k / digitBits) + k % digitBits = k := by
    simp only [digitBits]; omega
  rw [Num.shiftRight]
  split <;> rename_i h
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [h]; simp
    · rw [Num.val_isZero a h]; simp
  · split <;> rename_i h2
    · -- the shift clears every digit
      show denote #[0] = _
      rw [denote_singleton, show ((0 : Digit)).toNat = 0 from rfl]
      refine (Nat.div_eq_of_lt ?_).symm
      have h1 : a.val < base ^ a.digits.size := a.val_lt
      have h3 : base ^ a.digits.size ≤ 2 ^ k := by
        rw [base_pow]
        exact Nat.pow_le_pow_right (by omega) (by simp only [digitBits] at h2 ⊢; omega)
      omega
    · -- the general case: drop `k / 32` digits, then shift the rest
      have hw : k / digitBits ≤ a.digits.size := by omega
      have hext : (a.digits.extract (k / digitBits) a.digits.size).size
          = a.digits.size - k / digitBits := by simp
      have hsplit : a.val = denoteN a.digits (k / digitBits)
          + denote (a.digits.extract (k / digitBits) a.digits.size) * base ^ (k / digitBits) := by
        rw [Num.val, denote]
        exact denoteN_extract (j := k / digitBits) a.digits a.digits.size hw (Nat.le_refl _)
      have hlow : denoteN a.digits (k / digitBits) < base ^ (k / digitBits) :=
        denoteN_lt a.digits _
      have hdiv : a.val / base ^ (k / digitBits)
          = denote (a.digits.extract (k / digitBits) a.digits.size) := by
        rw [hsplit, Nat.add_mul_div_right _ _ (Nat.pow_pos (by simp [base])),
          Nat.div_eq_of_lt hlow, Nat.zero_add]
      rw [Num.val_ofArray,
        denote_shiftRightDigits _ hbit (by omega),
        show denoteN (a.digits.extract (k / digitBits) a.digits.size)
            (a.digits.size - k / digitBits)
          = denote (a.digits.extract (k / digitBits) a.digits.size) from by
            rw [denote, hext],
        ← hdiv, Nat.div_div_eq_div_mul, base_pow, ← Nat.pow_add, hk]

/-! ### Bitwise operations, as `mpz` implements them -/

/-- Digit `i` of a value, read off its denotation. -/
theorem denote_digit (a : Array Digit) (i : Nat) :
    denote a / base ^ i % base = (a.getD i 0).toNat := by
  have hb : base ^ (i+1) = base ^ i * base := Nat.pow_succ base i
  have hlow : denoteN a i < base ^ i := denoteN_lt a i
  rw [← Nat.mod_mul_right_div_self, ← hb, ← denoteN_mod, denoteN,
    Nat.add_mul_div_right _ _ (Nat.pow_pos (by simp [base])), Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- Bit `j` of a value is bit `j % 32` of its digit `j / 32`. -/
theorem testBit_denote (a : Array Digit) (j : Nat) :
    (denote a).testBit j = (a.getD (j / digitBits) 0).toNat.testBit (j % digitBits) := by
  obtain ⟨q, r, hr, hj⟩ : ∃ q r, r < 32 ∧ j = r + 32 * q :=
    ⟨j / 32, j % 32, Nat.mod_lt _ (by omega), by omega⟩
  subst hj
  have hq : (r + 32 * q) / digitBits = q := by simp only [digitBits]; omega
  have hrm : (r + 32 * q) % digitBits = r := by simp only [digitBits]; omega
  rw [hq, hrm, Nat.testBit_add, ← base_pow, ← denote_digit a q,
    show (base : Nat) = 2 ^ 32 from rfl, Nat.testBit_mod_two_pow]
  simp [hr]

/-- `mpz::operator&=` and friends: combine digits pointwise. -/
def bitwiseDigits (f : Digit → Digit → Digit) (a b : Array Digit) : Array Digit :=
  (Array.range (max a.size b.size)).map fun i => f (a.getD i 0) (b.getD i 0)

@[simp] theorem size_bitwiseDigits (f : Digit → Digit → Digit) (a b : Array Digit) :
    (bitwiseDigits f a b).size = max a.size b.size := by simp [bitwiseDigits]

private theorem getD_bitwiseDigits (f : Digit → Digit → Digit) (hf : f 0 0 = 0)
    (a b : Array Digit) (i : Nat) :
    (bitwiseDigits f a b).getD i 0 = f (a.getD i 0) (b.getD i 0) := by
  rcases Nat.lt_or_ge i (max a.size b.size) with h | h
  · rw [bitwiseDigits]; simp [h]
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

@[simp] theorem Num.val_land (a b : Num) : (a.land b).val = a.val &&& b.val := by
  rw [Num.land, Num.val_ofArray, denote_bitwiseDigits_and, Num.val, Num.val]

@[simp] theorem Num.val_lor (a b : Num) : (a.lor b).val = a.val ||| b.val := by
  rw [Num.lor, Num.val_ofArray, denote_bitwiseDigits_or, Num.val, Num.val]

@[simp] theorem Num.val_xor (a b : Num) : (a.xor b).val = a.val ^^^ b.val := by
  rw [Num.xor, Num.val_ofArray, denote_bitwiseDigits_xor, Num.val, Num.val]

/-! ### `gcd`, as `mpz` implements it -/

/--
Euclid's loop, as `gcd` in `mpz.cpp` runs it: replace the pair by the smaller
value and the remainder until the remainder is zero. It terminates because the
remainder is below the divisor.
-/
def Num.gcdLoop (a b : Num) : Num :=
  if b.val = 0 then a else Num.gcdLoop b (a.mod b)
termination_by b.val
decreasing_by
  rename_i hne
  rw [Num.val_mod a b hne]
  exact Nat.mod_lt _ (by omega)

/-- `gcd`: order the operands, then run Euclid. -/
def Num.gcd (a b : Num) : Num :=
  if Mpn.compare a.digits b.digits < 0 then Num.gcdLoop b a else Num.gcdLoop a b

private theorem Nat.gcd_step (m n : Nat) : Nat.gcd m n = Nat.gcd n (m % n) := by
  rw [Nat.gcd_comm m n, Nat.gcd_rec n m, Nat.gcd_comm]

theorem Num.val_gcdLoop (a b : Num) : (a.gcdLoop b).val = Nat.gcd a.val b.val := by
  rw [Num.gcdLoop]
  split <;> rename_i h
  · rw [h]; simp
  · rw [Num.val_gcdLoop b (a.mod b), Num.val_mod a b h, ← Nat.gcd_step]
termination_by b.val
decreasing_by
  rename_i hne
  rw [Num.val_mod a b hne]
  exact Nat.mod_lt _ (by omega)

/-- `gcd` computes the greatest common divisor. -/
theorem Num.val_gcd (a b : Num) : (a.gcd b).val = Nat.gcd a.val b.val := by
  rw [Num.gcd]
  split
  · rw [Num.val_gcdLoop, Nat.gcd_comm]
  · rw [Num.val_gcdLoop]

/-!
## Differential testing against `Nat`

`mpn_to_string` is not proved here; it is checked against `Nat` on pseudorandom
inputs instead, as are the proved routines. The digit
generator is biased towards `0`, `1` and `2^32-1` so that carries, borrows and
Knuth's quotient correction step fire often.
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
    let (q, r) := div a b
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
      let (q, r) := div a b
      IO.println (vec "quot" q)
      IO.println (vec "rem" r)
    IO.println s!"str {Mpn.toString a}"

/--
Print the `mpz`-layer results in the format `mpz_crosscheck.cpp` uses, so the
two can be diffed.
-/
def emitNum (trials : Nat) (maxLen : Nat) (seed : UInt64) : IO Unit := do
  let mut s := seed
  for t in [0:trials] do
    s := nextRand s
    let la := ((s >>> 33).toNat % maxLen) + 1
    s := nextRand s
    let lb := ((s >>> 33).toNat % maxLen) + 1
    let (da, s') := drawArray la s
    let (db, s'') := drawArray lb s'
    s := s''
    s := nextRand s
    let k := (s >>> 33).toNat % 100
    let A := Num.ofArray! da
    let B := Num.ofArray! db
    IO.println s!"case {t}"
    IO.println s!"a {A.val}"
    IO.println s!"b {B.val}"
    IO.println s!"add {(A.add B).val}"
    IO.println s!"sub {(A.sub B).val}"
    IO.println s!"mul {(A.mul B).val}"
    if B.val != 0 then
      IO.println s!"div {(A.div B).val}"
      IO.println s!"mod {(A.mod B).val}"
    IO.println s!"gcd {(A.gcd B).val}"
    IO.println s!"and {(A.land B).val}"
    IO.println s!"or {(A.lor B).val}"
    IO.println s!"xor {(A.xor B).val}"
    IO.println s!"shl {(A.shiftLeft k).val}"
    IO.println s!"shr {(A.shiftRight k).val}"
    IO.println s!"k {k}"

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
