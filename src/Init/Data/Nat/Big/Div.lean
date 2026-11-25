/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.Data.Nat.Big.Mul

/-!
# Big natural numbers: division

Long division (Knuth's algorithm D), Newton division, `divMod`, `gcd` and modular powers of
`BigNat`s.
-/

set_option compiler.extract_closed false

namespace Nat.Big

open BigNat

/-! ## Long division -/

@[inline, expose] public def BASE : UInt64 := 0x100000000

/-- Knuth's correction of the estimated quotient digit `qh`. The test cannot fire at `qh = 0`. -/
@[expose] public def recheck (qh rh vtop vsec unext : UInt64) : UInt64 :=
  if qh ≥ BASE || qh * vsec > (rh <<< 32) + unext then
    let qh' := qh - 1
    let rh' := rh + vtop
    if rh' < BASE then recheck qh' rh' vtop vsec unext else qh'
  else qh
termination_by qh.toNat
decreasing_by
  rename_i h _
  have hq : qh ≠ 0 := by
    intro h0; rw [h0] at h
    simp [BASE, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at h
  have h1 : qh.toNat ≠ 0 := fun h0 => hq (UInt64.toNat_inj.mp (by rw [h0]; rfl))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
  simp; omega


/-- `ms[0..n] := q * v[0..n)`. -/
@[expose] public def mul1Loop (q : UInt64) (v : BigNat) (n : USize) (hn : n.toNat ≤ v.n) (i : USize) (k : UInt64)
    (ms : BigNat) (hms : n.toNat < ms.n) (_hi : i.toNat ≤ n.toNat) : BigNat :=
  if h : i < n then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := q * (v.get i (by omega)).toUInt64 + k
    mul1Loop q v n hn (i+1) (t >>> 32) (ms.set i (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else ms.set n hms k.toUInt32
termination_by n.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[simp] public theorem n_mul1Loop (q v n hn i k ms hms hi) : (mul1Loop q v n hn i k ms hms hi).n = ms.n := by
  fun_induction mul1Loop q v n hn i k ms hms hi <;> simp_all

/-- `u[off..off+len) -= b[0..len)`, dropping the final borrow. -/
@[expose] public def subInPlace (b : BigNat) (len off : USize) (hb : len.toNat ≤ b.n) (i : USize) (k : UInt64) (u : BigNat)
    (hu : off.toNat + len.toNat ≤ u.n) (_hi : i.toNat ≤ len.toNat) : BigNat :=
  if h : i < len then
    have hi' := USize.lt_iff_toNat_lt.mp h
    have hoi : (off + i).toNat = off.toNat + i.toNat :=
      toNat_add_of_lt_size (by have := u.n_lt_size; omega)
    let t := (u.get (off + i) (by omega)).toUInt64 - (b.get i (by omega)).toUInt64 - k
    subInPlace b len off hb (i+1) (t >>> 63) (u.set (off + i) (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else u
termination_by len.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[simp] public theorem n_subInPlace (b len off hb i k u hu hi) :
    (subInPlace b len off hb i k u hu hi).n = u.n := by
  fun_induction subInPlace b len off hb i k u hu hi <;> simp_all

/-- `u[off..off+len) += v[0..len)` (reading digits of `v` past its end as `0`), dropping the final
carry. -/
@[expose] public def addInPlace (v : BigNat) (len off : USize) (i : USize) (k : UInt64) (u : BigNat)
    (hu : off.toNat + len.toNat ≤ u.n) (_hi : i.toNat ≤ len.toNat) : BigNat :=
  if h : i < len then
    have hi' := USize.lt_iff_toNat_lt.mp h
    have hoi : (off + i).toNat = off.toNat + i.toNat :=
      toNat_add_of_lt_size (by have := u.n_lt_size; omega)
    let t := (getOr0 v i).toUInt64 + (u.get (off + i) (by omega)).toUInt64 + k
    addInPlace v len off (i+1) (t >>> 32) (u.set (off + i) (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else u
termination_by len.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[simp] public theorem n_addInPlace (v len off i k u hu hi) : (addInPlace v len off i k u hu hi).n = u.n := by
  fun_induction addInPlace v len off i k u hu hi <;> simp_all

/-- Knuth's algorithm D on the normalized `u` and `v` (`n ≥ 2` digits). -/
@[expose] public def divNLoop (v : BigNat) (n : USize) (hn2 : 2 ≤ n.toNat) (hnv : n.toNat ≤ v.n) (vtop vsec : UInt64)
    (j1 : USize) (q u ms : BigNat) (hq : j1.toNat ≤ q.n) (hu : j1.toNat + n.toNat ≤ u.n)
    (hms : n.toNat < ms.n) : BigNat × BigNat :=
  if h : j1 = 0 then (q, u) else
    have hj1 : 0 < j1.toNat := by
      have : j1.toNat ≠ 0 := fun h' => h (USize.toNat_inj.mp (by simpa using h'))
      omega
    let j := j1 - 1
    have hj : j.toNat = j1.toNat - 1 := toNat_pred hj1
    have hjn : (j + n).toNat = j.toNat + n.toNat :=
      toNat_add_of_lt_size (by have := u.n_lt_size; omega)
    have hjn1 : (j + n - 1).toNat = j.toNat + n.toNat - 1 := by rw [toNat_pred (by omega), hjn]
    have hjn2 : (j + n - 2).toNat = j.toNat + n.toNat - 2 := by rw [toNat_sub_two (by omega), hjn]
    let temp := ((u.get (j + n) (by omega)).toUInt64 <<< 32) ||| (u.get (j + n - 1) (by omega)).toUInt64
    let qh := recheck (temp / vtop) (temp % vtop) vtop vsec (u.get (j + n - 2) (by omega)).toUInt64
    let ms1 := mul1Loop qh v n hnv 0 0 ms hms (by simp)
    have hms1 : n.toNat < ms1.n := by simp [ms1]; omega
    have hn1 : (n + 1).toNat = n.toNat + 1 := toNat_succ_of_lt_size (by have := ms.n_lt_size; omega)
    let u1 := subInPlace ms1 (n + 1) j (by rw [hn1]; omega) 0 0 u (by rw [hn1]; omega) (by simp)
    have hu1 : j1.toNat + n.toNat ≤ u1.n := by simp [u1]; omega
    if u1.get (j + n) (by omega) != 0 then
      divNLoop v n hn2 hnv vtop vsec j (q.set j (by omega) (qh.toUInt32 - 1))
        (addInPlace v (n + 1) j 0 0 u1 (by rw [hn1]; omega) (by simp)) ms1 (by simp; omega)
        (by simp; omega) hms1
    else
      divNLoop v n hn2 hnv vtop vsec j (q.set j (by omega) qh.toUInt32) u1 ms1 (by simp; omega)
        (by omega) hms1
termination_by j1.toNat
decreasing_by all_goals (rw [toNat_pred hj1]; omega)

@[simp] public theorem n_divNLoop_snd (v n hn2 hnv vtop vsec j1 q u ms hq hu hms) :
    (divNLoop v n hn2 hnv vtop vsec j1 q u ms hq hu hms).2.n = u.n := by
  fun_induction divNLoop v n hn2 hnv vtop vsec j1 q u ms hq hu hms <;> simp_all +zetaDelta

/-- The divisor shifted left by `s < 32`. -/
@[inline, expose] public def shiftDivisor (b : BigNat) (lb : USize) (hlb : lb.toNat = b.n) (s : UInt32)
    (h : (lb.toNat + 1) * 4 ≤ maxBytes) : {v : BigNat // lb.toNat ≤ v.n} :=
  have hlb1 : (lb + 1).toNat = lb.toNat + 1 := toNat_succ_of_lt_size (by have := maxBytes_lt; omega)
  if s == 0 then ⟨b, by omega⟩
  else ⟨shlLoop b lb 0 s 0 hlb 0 (zeros (lb + 1) (by omega))
      (by simp only [n_zeros, USize.toNat_zero, Nat.zero_add]; omega) (by simp),
    by simp only [n_zeros, n_shlLoop]; omega⟩

/-- The dividend shifted left by `s < 32`, with one more digit. -/
@[inline, expose] public def shiftDividend (a : BigNat) (la : USize) (hla : la.toNat = a.n) (s : UInt32)
    (h : (la.toNat + 1) * 4 ≤ maxBytes) : {u : BigNat // u.n = la.toNat + 1} :=
  have hla1 : (la + 1).toNat = la.toNat + 1 := toNat_succ_of_lt_size (by have := maxBytes_lt; omega)
  if s == 0 then
    ⟨copyLoop a la 0 0 hla (zeros (la + 1) (by omega))
      (by simp only [n_zeros, USize.toNat_zero, Nat.zero_add]; omega) (by simp),
      by simp only [n_zeros, n_copyLoop]; omega⟩
  else
    ⟨shlLoop a la 0 s 0 hla 0 (zeros (la + 1) (by omega))
      (by simp only [n_zeros, USize.toNat_zero, Nat.zero_add]; omega) (by simp),
      by simp only [n_zeros, n_shlLoop]; omega⟩

/-- The low `lb` digits of `u`, shifted right by `s < 32`. -/
@[inline, expose] public def knuthRem (u : BigNat) (lb : USize) (hlb : lb.toNat ≤ u.n) (s : UInt32)
    (h : lb.toNat * 4 ≤ maxBytes) : BigNat :=
  if s == 0 then u.take lb hlb
  else shrLoop (u.take lb hlb) 0 lb s (by simp) 0 (zeros lb h) (by simp) (by simp)

/-- Algorithm D on the operands `v` and `u`, already shifted left by `s`. -/
@[inline, expose] public def knuthCore (a b : BigNat) (h : 2 ≤ b.n ∧ b.n ≤ a.n ∧ (a.n + 1) * 4 ≤ maxBytes) (s : UInt32)
    (v : {v : BigNat // b.usize.toNat ≤ v.n}) (u : {u : BigNat // u.n = a.usize.toNat + 1}) : BigNat × BigNat :=
  have hla : a.usize.toNat = a.n := a.usize_toNat
  have hlb : b.usize.toNat = b.n := b.usize_toNat
  have hb2 := h.1
  have hba := h.2.1
  have hfit := h.2.2
  have hlb1 : (b.usize - 1).toNat = b.usize.toNat - 1 := toNat_pred (by omega)
  have hlb2 : (b.usize - 2).toNat = b.usize.toNat - 2 := toNat_sub_two (by omega)
  have hlb1' : (b.usize + 1).toNat = b.usize.toNat + 1 := by rw [hlb]; exact b.usize_succ_toNat
  have hm : (a.usize - b.usize).toNat = a.usize.toNat - b.usize.toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))
  have hm1 : (a.usize - b.usize + 1).toNat = a.usize.toNat - b.usize.toNat + 1 := by
    rw [toNat_succ_of_lt_size (by have := maxBytes_lt; omega), hm]
  let p := divNLoop v.1 b.usize (by omega) v.2 (v.1.get (b.usize - 1) (by have := v.2; omega)).toUInt64
    (v.1.get (b.usize - 2) (by have := v.2; omega)).toUInt64 (a.usize - b.usize + 1)
    (zeros (a.usize - b.usize + 1) (by omega)) u.1 (zeros (b.usize + 1) (by omega)) (by simp)
    (by have := u.2; omega) (by simp only [n_zeros]; omega)
  have hp : b.usize.toNat ≤ p.2.n := by simp only [p, n_divNLoop_snd]; have := u.2; omega
  (p.1.normalize, (knuthRem p.2 b.usize hp s (by omega)).normalize)

/-- Knuth's algorithm D for `2 ≤ b.n ≤ a.n`. -/
@[expose] public def knuth (a b : BigNat) (h : 2 ≤ b.n ∧ b.n ≤ a.n ∧ (a.n + 1) * 4 ≤ maxBytes) : BigNat × BigNat :=
  have hlb : b.usize.toNat = b.n := b.usize_toNat
  have hla : a.usize.toNat = a.n := a.usize_toNat
  have hlb1 : (b.usize - 1).toNat = b.usize.toNat - 1 := toNat_pred (by omega)
  -- normalize so that the top digit of the divisor has its high bit set
  let s := 31 - (b.get (b.usize - 1) (by omega)).log2
  knuthCore a b h s (shiftDivisor b b.usize hlb s (by omega)) (shiftDividend a a.usize hla s (by omega))

/-- Quotient and remainder by long division; `b = 0` gives `(0, a)`. -/
@[expose] public def divModBasecase (a b : BigNat) : BigNat × BigNat :=
  if cmp a b == .lt then (empty, a)
  else if h1 : b.usize = 1 then
    let p := divModSmall a (b.get 0 (by have := b.usize_toNat; rw [h1] at this; simp at this ⊢; omega))
    (p.1, ofUInt64 p.2.toUInt64)
  else if h : 2 ≤ b.n ∧ b.n ≤ a.n then
    if h' : (a.n + 1) * 4 ≤ maxBytes then knuth a b ⟨h.1, h.2, h'⟩ else panic! "out of memory"
  else (empty, a)


/-! ## Newton division -/

@[inline, expose] public def bitLen (a : BigNat) : USize :=
  let n := a.usize
  if h : n = 0 then 0
  else
    have hn : 0 < n.toNat := by
      have : n.toNat ≠ 0 := fun h' => h (USize.toNat_inj.mp (by simpa using h'))
      omega
    ((n - 1) <<< 5) + (a.get (n - 1) (by rw [toNat_pred hn, a.usize_toNat] at *; omega)).log2.toUSize + 1

@[inline, expose] public def pow2 (k : USize) : BigNat := shiftLeft (ofUInt64 1) k

/--
Approximates `2^(m + L) / b`, where `m` is the bit length of `b`, by Newton iteration, using only the
top `L + 64` bits of `b`. Division only relies on the result through checked corrections.
-/
@[expose] public def recip (b : BigNat) (L : USize) : BigNat :=
  let m := bitLen b
  let b := if m > L + 64 then shiftRight b (m - (L + 64)) else b
  let m := bitLen b
  if _hL : L < 2048 then (divModBasecase (pow2 (m + L)) b).1
  else
    let h := (L >>> 1) + 1
    -- `y ≈ 2^(m + h) / b`
    let y := recip b h
    -- one Newton step: `x = y 2^(L-h) + y (2^(m+h) - b y) / 2^(m + 2h - L)`
    let t := pow2 (m + h)
    let p := mul b y
    let sh := m + 2 * h - L
    let base := shiftLeft y (L - h)
    if cmp p t != .gt then add base (shiftRight (mul y (sub t p)) sh)
    else
      let d := shiftRight (mul y (sub p t)) sh
      if cmp d base == .gt then empty else sub base d
termination_by L.toNat
decreasing_by
  have hL' := not_lt_toNat _hL
  have e : (2048 : USize).toNat = 2048 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h]
  have e1 : (1 : USize).toNat % System.Platform.numBits = 1 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  have hs : (L >>> 1).toNat = L.toNat / 2 := by
    rw [USize.toNat_shiftRight, e1, Nat.shiftRight_eq_div_pow]
  have := L.toNat_lt_size
  rw [toNat_succ_of_lt_size (by omega), hs]
  omega

/-- Steps the quotient estimate `q` (with `qb = q * b > a`) down. -/
@[expose] public def newtonDown (a b : BigNat) (fuel : Nat) (q qb : BigNat) : BigNat × BigNat :=
  let q := sub q (ofUInt64 1)
  let qb := sub qb b
  if cmp qb a == .gt then
    match fuel with
    | 0 => divModBasecase a b
    | fuel + 1 => newtonDown a b fuel q qb
  else (q, sub a qb)

/-- Steps the quotient estimate `q` (with `q * b + r = a`) up. -/
@[expose] public def newtonUp (a b : BigNat) (fuel : Nat) (q r : BigNat) : BigNat × BigNat :=
  if cmp r b != .lt then
    match fuel with
    | 0 => divModBasecase a b
    | fuel + 1 => newtonUp a b fuel (add q (ofUInt64 1)) (sub r b)
  else (q, r)

/--
Corrects the quotient estimate `q` to the exact quotient and remainder. The size check, which a
good estimate always passes, keeps `mul q b` from overflowing.
-/
@[inline, expose] public def newtonFinish (a b q : BigNat) : BigNat × BigNat :=
  if q.n + b.n ≤ a.n + 2 then
    let qb := mul q b
    if cmp qb a == .gt then newtonDown a b 64 q qb else newtonUp a b 64 q (sub a qb)
  else divModBasecase a b

/-- Quotient and remainder by `b ≠ 0` via a Newton reciprocal, for `b ≤ a`. -/
@[expose] public def divModNewton (a b : BigNat) : BigNat × BigNat :=
  let m := bitLen b
  let n := bitLen a
  let L := n - m + 1
  let x := recip b L
  -- only the top `L + 64` bits of `a` affect the quotient beyond the final correction
  let s := if n > L + 64 then n - (L + 64) else 0
  newtonFinish a b (shiftRight (mul (shiftRight a s) x) (m + L - s))

/--
Quotient and remainder. Uses Newton division if both `b` and the quotient have at least 24576 bits
(above the measured break-even point), and long division otherwise.
-/
@[expose] public def divMod (a b : BigNat) : BigNat × BigNat :=
  let m := bitLen b
  let n := bitLen a
  if m ≥ 24576 && n ≥ m + 24576 then divModNewton a b else divModBasecase a b


/-! ## Greatest common divisor -/

/--
Euclid's algorithm with a step budget. Two steps at least halve the remainder, so the budget of
`gcd` always suffices for normalized inputs.
-/
@[expose] public def gcdLoop : Nat → BigNat → BigNat → BigNat
  | 0, a, _ => a
  | fuel + 1, a, b => if b.usize == 0 then a else gcdLoop fuel b (divMod a b).2

@[expose] public def gcd (a b : BigNat) : BigNat := gcdLoop (64 * (a.n + b.n) + 2) a b

/-! ## Modular powers -/

@[expose] public def powModLoop (e m : BigNat) (nbits i : USize) (base acc : BigNat) : BigNat :=
  if h : i < nbits then
    let bit := (getOr0 e (i >>> 5) >>> (i &&& 31).toUInt32) &&& 1
    let acc := if bit == 1 then (divMod (mul acc base) m).2 else acc
    let base := if i + 1 < nbits then (divMod (mul base base) m).2 else base
    powModLoop e m nbits (i + 1) base acc
  else acc
termination_by nbits.toNat - i.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.mp h
  rw [toNat_succ_of_lt_size (by have := nbits.toNat_lt_size; omega)]; omega

/-- `a ^ e % m` for `m > 1`. -/
@[expose] public def powMod (a e m : BigNat) : BigNat :=
  if e.usize == 0 then ofUInt64 1
  else powModLoop e m (log2 e + 1) 0 (divMod a m).2 (ofUInt64 1)

end Nat.Big
