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

/--
`div_normalize`. Returns the shift `d` together with the normalized numerator
(`lnum+1` digits) and denominator (`lden` digits).

NOTE: the C++ `while (lden > 0 && ((denom[lden-1] << d) & MASK_FIRST) == 0) d++;`
shifts by `d == 32` once the top denominator digit is zero, which is undefined
behaviour. The bounded loop below stops at 32 instead. Callers reach `mpn_div`
only through `mpz`, whose sizes are normalized, so the top digit is nonzero
unless the denominator is zero.
-/
def divNormalize (numer denom : Array Digit) : Nat × Array Digit × Array Digit := Id.run do
  let lnum := numer.size
  let lden := denom.size
  let mut d := 0
  if lden > 0 then
    for i in [0:digitBits] do
      if (denom[lden-1]! <<< (UInt32.ofNat i)) &&& maskFirst == 0 then d := d + 1 else break
  let mut n_numer : Array Digit := Array.replicate (lnum + 1) 0
  let mut n_denom : Array Digit := Array.replicate lden 0
  if d == 0 then
    for i in [0:lnum] do n_numer := n_numer.set! i numer[i]!
    for i in [0:lden] do n_denom := n_denom.set! i denom[i]!
  else if lnum != 0 then
    let sh : Digit := UInt32.ofNat d
    let firstBits (x : Digit) : Digit := x >>> (UInt32.ofNat (digitBits - d))
    n_numer := n_numer.set! lnum (firstBits numer[lnum-1]!)
    for k in [0:lnum-1] do
      let i := lnum - 1 - k
      n_numer := n_numer.set! i ((numer[i]! <<< sh) ||| firstBits numer[i-1]!)
    n_numer := n_numer.set! 0 (numer[0]! <<< sh)
    for k in [0:lden-1] do
      let i := lden - 1 - k
      n_denom := n_denom.set! i ((denom[i]! <<< sh) ||| firstBits denom[i-1]!)
    if lden > 0 then n_denom := n_denom.set! 0 (denom[0]! <<< sh)
  else
    d := 0
  return (d, n_numer, n_denom)

/-- `div_unnormalize`. Produces `lden` remainder digits. -/
def divUnnormalize (numer : Array Digit) (lden d : Nat) : Array Digit := Id.run do
  let mut rem : Array Digit := Array.replicate lden 0
  if d == 0 then
    for i in [0:lden] do rem := rem.set! i (numer.getD i 0)
  else
    let sh : Digit := UInt32.ofNat d
    let lastBits (x : Digit) : Digit :=
      (x <<< (UInt32.ofNat (digitBits - d))) >>> (UInt32.ofNat (digitBits - d))
    for i in [0:lden-1] do
      rem := rem.set! i ((numer.getD i 0 >>> sh) |||
        (lastBits (numer.getD (i+1) 0) <<< (UInt32.ofNat (digitBits - d))))
    rem := rem.set! (lden-1) (numer.getD (lden-1) 0 >>> sh)
  return rem

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
