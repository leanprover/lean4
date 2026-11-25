/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.Data.Nat.Big.Basic
import all Init.Data.ByteArray.Extra

/-!
# Big natural numbers: multiplication

Schoolbook and Karatsuba multiplication of `BigNat`s, and powers.
-/

set_option compiler.extract_closed false

namespace Nat.Big

open BigNat

/-! ## Multiplication -/

/-- `c[j..] += a * v`, writing the final carry to `c[j + la]`. -/
@[expose] public def mulInner (a : BigNat) (la j : USize) (hla : la.toNat = a.n) (v : UInt64) (i : USize) (k : UInt64)
    (c : BigNat) (hc : j.toNat + la.toNat < c.n) (_hi : i.toNat ≤ la.toNat) : BigNat :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    have hij : (i + j).toNat = i.toNat + j.toNat := toNat_add_of_lt_size (by
      have := c.n_lt_size; omega)
    let t := (a.get i (by omega)).toUInt64 * v + (c.get (i + j) (by omega)).toUInt64 + k
    mulInner a la j hla v (i+1) (t >>> 32) (c.set (i + j) (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else
    have hjl : (j + la).toNat = j.toNat + la.toNat := toNat_add_of_lt_size (by
      have := c.n_lt_size; omega)
    c.set (j + la) (by omega) k.toUInt32
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[simp] public theorem n_mulInner (a : BigNat) (la j hla v i k c hc hi) :
    (mulInner a la j hla v i k c hc hi).n = c.n := by
  fun_induction mulInner a la j hla v i k c hc hi with
  | case1 i k c hc hi h _ _ _ ih => rw [ih]; simp
  | case2 => simp

@[expose] public def mulOuter (a b : BigNat) (la lb j : USize) (hla : la.toNat = a.n) (hlb : lb.toNat = b.n)
    (c : BigNat) (hc : a.n + b.n ≤ c.n) (_hj : j.toNat ≤ lb.toNat) : BigNat :=
  if h : j < lb then
    have hj' := USize.lt_iff_toNat_lt.mp h
    let v := b.get j (by omega)
    mulOuter a b la lb (j+1) hla hlb
      (if v == 0 then c else mulInner a la j hla v.toUInt64 0 0 c (by omega) (by simp))
      (by split <;> simp_all [n_mulInner]) (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by lb.toNat - j.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega


public theorem BigNat.usize_add_toNat (a b : BigNat) (h : (a.n + b.n) * 4 ≤ maxBytes) :
    (a.usize + b.usize).toNat = a.n + b.n := by
  have := maxBytes_lt
  rw [toNat_add_of_lt_size (by rw [usize_toNat, usize_toNat]; omega), usize_toNat, usize_toNat]

/-- Schoolbook `a * b`, with `a.n + b.n` digits (not normalized). -/
@[expose] public def mulCore (a b : BigNat) (h : (a.n + b.n) * 4 ≤ maxBytes) : BigNat :=
  mulOuter a b a.usize b.usize 0 (usize_toNat a) (usize_toNat b)
    (zeros (a.usize + b.usize) (by rw [BigNat.usize_add_toNat a b h]; exact h))
    (by rw [n_zeros, BigNat.usize_add_toNat a b h]; omega) (by simp)

/-- Schoolbook multiplication; panics if the result would exceed `maxBytes`. -/
@[expose] public def mulBasecase (a b : BigNat) : BigNat :=
  if h : (a.n + b.n) * 4 ≤ maxBytes then
    -- the longer operand goes into the inner loop
    if b.n ≤ a.n then (mulCore a b h).normalize else (mulCore b a (by omega)).normalize
  else panic! "out of memory"


/-! ## Karatsuba multiplication -/

public theorem n_normalize_le (a : BigNat) : a.normalize.n ≤ a.n := by
  have := a.topNonzero_le a.usize a.usize_le
  simp only [normalize, n_take]
  rw [a.usize_toNat] at this
  exact this

public theorem n_panic (msg : String) : (panic msg : BigNat).n = 0 := by unfold panic panicCore; rfl

public theorem not_le_toNat {i n : USize} (h : ¬ i ≤ n) : n.toNat < i.toNat := by
  have : ¬ i.toNat ≤ n.toNat := fun h' => h (USize.le_iff_toNat_le.mpr h')
  omega

@[simp] public theorem n_addTail (a la i hla k c hc hi) : (addTail a la i hla k c hc hi).n = c.n := by
  fun_induction addTail a la i hla k c hc hi <;> simp_all

@[simp] public theorem n_addLoop (a b la lb i hla hlb hab k c hc hi) :
    (addLoop a b la lb i hla hlb hab k c hc hi).n = c.n := by
  fun_induction addLoop a b la lb i hla hlb hab k c hc hi <;> simp_all

public theorem n_addCore (a b hab h) : (addCore a b hab h).n = a.n + 1 := by
  simp only [addCore, n_addLoop, n_zeros, usize_succ_toNat]

public theorem n_add_le (a b : BigNat) : (add a b).n ≤ max a.n b.n + 1 := by
  unfold add
  split
  · split
    · have := n_normalize_le (addCore a b ‹_› ‹_›); rw [n_addCore] at this; omega
    · simp [panicWithPosWithDecl, n_panic]
  · split
    · have := n_normalize_le (addCore b a (by omega) ‹_›); rw [n_addCore] at this; omega
    · simp [panicWithPosWithDecl, n_panic]

/-- Digits `[lo, hi)` of `a` for `lo ≤ hi ≤ a.n`. -/
@[inline, expose] public def extractDigits (a : BigNat) (lo hi : USize) (h1 : lo.toNat ≤ hi.toNat) (h2 : hi.toNat ≤ a.n) :
    BigNat where
  bytes := a.bytes.extract (lo <<< 2).toNat (hi <<< 2).toNat
  size_mod := by
    have := maxBytes_lt; have := a.n_le
    rw [ByteArray.size_extract, shiftLeft_toNat lo (by omega), shiftLeft_toNat hi (by omega),
      ← a.n_mul_four]
    omega
  size_le := by
    have := a.size_le
    rw [ByteArray.size_extract]
    omega

@[simp] public theorem n_extractDigits (a : BigNat) (lo hi h1 h2) :
    (extractDigits a lo hi h1 h2).n = hi.toNat - lo.toNat := by
  have := maxBytes_lt; have := a.n_le
  have h := (extractDigits a lo hi h1 h2).n_mul_four
  have hs : (extractDigits a lo hi h1 h2).bytes.size = min (hi.toNat * 4) (a.n * 4) - lo.toNat * 4 := by
    simp only [extractDigits, ByteArray.size_extract, shiftLeft_toNat lo (by omega),
      shiftLeft_toNat hi (by omega), ← a.n_mul_four]
  omega

/-- `min hi a.usize`. -/
@[inline, expose] public def clampHi (a : BigNat) (hi : USize) : {h : USize // h.toNat = min hi.toNat a.n} :=
  if h : hi ≤ a.usize then
    ⟨hi, by have := USize.le_iff_toNat_le.mp h; rw [a.usize_toNat] at this; omega⟩
  else ⟨a.usize, by have := not_le_toNat h; rw [a.usize_toNat] at this ⊢; omega⟩

/-- Digits `[lo, min hi a.n)` of `a`, normalized. -/
@[expose] public def slice (a : BigNat) (lo hi : USize) : BigNat :=
  let hi' := clampHi a hi
  if h : hi'.1 ≤ lo then empty
  else (extractDigits a lo hi'.1 (by have := not_le_toNat h; omega) (by rw [hi'.2]; omega)).normalize

public theorem n_slice_le (a : BigNat) (lo hi : USize) :
    (slice a lo hi).n ≤ hi.toNat - lo.toNat ∧ (slice a lo hi).n ≤ a.n - lo.toNat := by
  have hc := (clampHi a hi).2
  unfold slice
  dsimp only
  split
  · have : (empty : BigNat).n = 0 := rfl
    omega
  · next h =>
    have h1 := n_normalize_le (extractDigits a lo (clampHi a hi).1 (by have := not_le_toNat h; omega)
      (by rw [hc]; omega))
    rw [n_extractDigits] at h1
    omega

/-- `a * 2^(32 k)`; panics if the result would exceed `maxBytes`. -/
@[inline, expose] public def shiftDigits (a : BigNat) (k : USize) : BigNat :=
  if a.usize == 0 then a else
  if h : (a.n + k.toNat) * 4 ≤ maxBytes then
    have hk : (a.usize + k).toNat = a.n + k.toNat := by
      rw [toNat_add_of_lt_size (by have := maxBytes_lt; rw [a.usize_toNat]; omega), a.usize_toNat]
    let c := zeros (a.usize + k) (by rw [hk]; exact h)
    { bytes := a.bytes.copySlice 0 c.bytes (k <<< 2).toNat (a.usize <<< 2).toNat
      size_mod := by
        have := maxBytes_lt
        rw [ByteArray.copySlice_eq_append]
        simp only [ByteArray.size_append, ByteArray.size_extract, c, zeros, size_replicate,
          shiftLeft_toNat k (by omega), shiftLeft_toNat a.usize (by rw [a.usize_toNat]; omega), hk,
          a.usize_toNat, ← a.n_mul_four, ByteArray.size_data]
        omega
      size_le := by
        have := maxBytes_lt
        rw [ByteArray.copySlice_eq_append]
        simp only [ByteArray.size_append, ByteArray.size_extract, c, zeros, size_replicate,
          shiftLeft_toNat k (by omega), shiftLeft_toNat a.usize (by rw [a.usize_toNat]; omega), hk,
          a.usize_toNat, ← a.n_mul_four, ByteArray.size_data]
        omega }
  else panic! "out of memory"

/-- Karatsuba multiplication, falling back to `mulBasecase` below 48 digits. -/
@[expose] public def mul (a b : BigNat) : BigNat :=
  if h : a.usize < b.usize then mul b a
  else if hb : b.usize < 48 then mulBasecase a b
  else
    have ha := a.usize_toNat
    have hb' := b.usize_toNat
    have h1 := not_lt_toNat h
    have h2 := not_lt_toNat hb
    let m := a.usize >>> 1
    have hm : m.toNat = a.n / 2 := by
      have : (1 : USize).toNat % System.Platform.numBits = 1 := by
        rcases System.Platform.numBits_eq with h | h <;> simp [h]
      simp only [m]; rw [USize.toNat_shiftRight, this, Nat.shiftRight_eq_div_pow, ha]
    let a0 := slice a 0 m
    let a1 := slice a m a.usize
    have ha0 := n_slice_le a 0 m
    have ha1 := n_slice_le a m a.usize
    if hbm : b.usize ≤ m then
      -- `b` fits into the low half, so there is no product of high halves
      add (shiftDigits (mul a1 b) m) (mul a0 b)
    else
      let b0 := slice b 0 m
      let b1 := slice b m b.usize
      have hb0 := n_slice_le b 0 m
      have hb1 := n_slice_le b m b.usize
      let z0 := mul a0 b0
      let z2 := mul a1 b1
      let z1 := sub (sub (mul (add a0 a1) (add b0 b1)) z0) z2
      add (add (shiftDigits z2 (m <<< 1)) (shiftDigits z1 m)) z0
termination_by (a.n + b.n, if a.n < b.n then 1 else 0)
decreasing_by
  all_goals try simp only [USize.toNat_zero, Nat.sub_zero] at *
  · have := USize.lt_iff_toNat_lt.mp h
    rw [a.usize_toNat, b.usize_toNat] at this
    apply Prod.Lex.right'
    · omega
    · simp only [this, ite_true]; split <;> omega
  all_goals
    have hm' : (a.usize >>> 1).toNat = a.n / 2 := hm
    have e48 : (48 : USize).toNat = 48 := by
      rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h]
    have ha0' := n_slice_le a 0 (a.usize >>> 1)
    have ha1' := n_slice_le a (a.usize >>> 1) a.usize
    have hb0' := n_slice_le b 0 (a.usize >>> 1)
    have hb1' := n_slice_le b (a.usize >>> 1) b.usize
    have e1 := n_add_le (slice a 0 (a.usize >>> 1)) (slice a (a.usize >>> 1) a.usize)
    have e2 := n_add_le (slice b 0 (a.usize >>> 1)) (slice b (a.usize >>> 1) b.usize)
    simp only [USize.toNat_zero, Nat.sub_zero] at ha0' hb0'
    rw [e48] at h2
    apply Prod.Lex.left
    first
      | (have hbm' : b.usize.toNat ≤ (a.usize >>> 1).toNat := USize.le_iff_toNat_le.mp hbm; omega)
      | (have hbm' : (a.usize >>> 1).toNat < b.usize.toNat := not_le_toNat hbm; omega)


/-! ## Powers -/

@[expose] public def powLoop (base : BigNat) (e : USize) (acc : BigNat) : BigNat :=
  if _h : e = 0 then acc else
    let acc := if e &&& 1 == 1 then mul acc base else acc
    if e == 1 then acc else powLoop (mul base base) (e >>> 1) acc
termination_by e.toNat
decreasing_by
  have : e.toNat ≠ 0 := fun h' => _h (USize.toNat_inj.mp (by simpa using h'))
  have e1 : (1 : USize).toNat % System.Platform.numBits = 1 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  rw [USize.toNat_shiftRight, e1, Nat.shiftRight_eq_div_pow]
  omega

@[expose] public def pow (a : BigNat) (e : USize) : BigNat := powLoop a e (ofUInt64 1)

end Nat.Big
