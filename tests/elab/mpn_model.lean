/-!
# Lean transliteration of the runtime's GMP-free bignum core

`src/runtime/mpn.cpp` implements multi-precision naturals as little-endian
arrays of `uint32_t` digits. It is the arithmetic Lean uses when built with
`USE_GMP=OFF` (the 32-bit and WebAssembly targets); both of those CI
configurations are currently disabled, so the code has no automated coverage.

This file transliterates it statement by statement so that the algorithms can
be checked against `Nat`, which is what `#eval mpnCheck` at the bottom does, and
so that they can be proved correct, which `denote_add` and `denote_sub` do for
`mpn_add` and `mpn_sub`. Deviations from the C++ are marked `NOTE:`.

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

/-- `mpn_mul`. Returns `lnga + lngb` digits. -/
def mul (a b : Array Digit) : Array Digit := Id.run do
  let lnga := a.size
  let lngb := b.size
  -- the C++ zeroes only `c[0..lnga)`; every later digit is written below
  let mut c : Array Digit := Array.replicate (lnga + lngb) 0
  for j in [0:lngb] do
    let v_j := b[j]!
    if v_j == 0 then
      c := c.set! (j + lnga) 0
    else
      let mut k : Digit := 0
      for i in [0:lnga] do
        let u_i := a[i]!
        let t : DoubleDigit :=
          u_i.toUInt64 * v_j.toUInt64 + (c.getD (i + j) 0).toUInt64 + k.toUInt64
        c := c.set! (i + j) (lo t)
        k := hi t
      c := c.set! (j + lnga) k
  return c

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

/-!
## Differential testing against `Nat`

`mpn_sub`, `mpn_mul`, `mpn_div` and `mpn_to_string` are not proved here; they
are checked against `Nat` on pseudorandom inputs instead. The digit generator
is biased towards `0`, `1` and `2^32-1` so that carries, borrows and Knuth's
quotient correction step fire often.
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
