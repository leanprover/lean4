/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.Data.ByteArray.Lemmas
public import Init.Data.ByteArray.Extra
public import Init.Data.String.Defs
public import Init.Data.Ord.Basic
public import Init.Data.UInt.Log2
public import Init.Data.UInt.Basic
public import Init.Data.Repr
public import Init.Data.Array.Basic
import all Init.Data.ByteArray.Extra
public import Init.Omega
public import Init.ByCases
public import Init.Data.UInt.Lemmas
public import Init.Data.UInt.Bitwise
public import Init.Data.Nat.Lemmas
public import Init.Data.Nat.Bitwise.Lemmas
public import Init.Data.Array.Lemmas
public import Init.Data.String.Length

/-!
# Big number magnitudes

The runtime represents a natural number that does not fit into a scalar as a `ByteArray` of
little-endian 32-bit digits without leading zero digits (a *magnitude*). This module implements
arithmetic on magnitudes; `Init.Data.Nat.BigRuntime` builds the runtime's big `Nat` and `Int`
primitives on top of it, and `Std.Data.Nat.Big` proves the operations correct.

A `Mag` bounds its size so that digit offsets never overflow `USize`, and digit accesses carry their
bounds as proofs, which are erased at runtime. The operations must not create big `Nat`s
themselves, as that would call back into them, so all counting at runtime uses `USize`. They are
called while `Init.Prelude` is being initialized, so they must not refer to module-level constants;
closed terms are therefore not extracted.
-/

set_option compiler.extract_closed false

namespace Nat.Big

/--
The largest byte size of a magnitude, `2 ^ (System.Platform.numBits - 4)`, far below `USize.size`.
It is computed without module-level constants or literals of `2 ^ 32` and above, which the runtime
would parse with these very functions.
-/
@[inline, expose] public def maxBytes : Nat :=
  if System.Platform.numBits = 64 then ((1 : USize) <<< 60).toNat else 268435456

public theorem maxBytes_eq : maxBytes = 2 ^ (System.Platform.numBits - 4) := by
  have e : USize.size = 2 ^ System.Platform.numBits := rfl
  rcases System.Platform.numBits_eq with h | h
  · simp [maxBytes, h]
  · simp only [maxBytes, h, ite_true, USize.toNat_shiftLeft, USize.toNat_one]
    rw [show (60 : USize).toNat = 60 by simp [USize.toNat_ofNat, h]]
    simp

public theorem maxBytes_lt : maxBytes * 8 < USize.size := by
  have : USize.size = 2 ^ System.Platform.numBits := rfl
  rcases System.Platform.numBits_eq with h | h <;> simp [maxBytes, this, h]

public theorem one_le_maxBytes : 1 ≤ maxBytes := by rw [maxBytes_eq]; exact Nat.one_le_two_pow

public structure Mag where
  bytes : ByteArray
  size_mod : bytes.size % 4 = 0
  size_le : bytes.size ≤ maxBytes

public theorem toNat_succ_of_lt {i n : USize} (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  have h1 := USize.lt_iff_toNat_lt.mp h
  have h2 := USize.toNat_lt_size n
  rw [USize.toNat_add, USize.toNat_one, ← USize.size_eq_two_pow, Nat.mod_eq_of_lt (by omega)]

public theorem toNat_succ_of_lt_size {x : USize} (h : x.toNat + 1 < USize.size) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [USize.toNat_add, USize.toNat_one, ← USize.size_eq_two_pow, Nat.mod_eq_of_lt h]

public theorem toNat_pred {i : USize} (h : 0 < i.toNat) : (i - 1).toNat = i.toNat - 1 := by
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by simp; omega)), USize.toNat_one]

public theorem not_lt_toNat {i n : USize} (h : ¬ i < n) : n.toNat ≤ i.toNat := by
  have : ¬ i.toNat < n.toNat := fun h' => h (USize.lt_iff_toNat_lt.mpr h')
  omega

namespace Mag

/-- The number of digits. -/
@[expose] public def n (a : Mag) : Nat := a.bytes.size / 4

public theorem n_mul_four (a : Mag) : a.n * 4 = a.bytes.size := by
  have := a.size_mod; simp only [n]; omega

public theorem n_le (a : Mag) : a.n * 4 ≤ maxBytes := by rw [n_mul_four]; exact a.size_le

public theorem two_toNat_mod : (2 : USize).toNat % System.Platform.numBits = 2 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

public theorem bytes_usize_toNat (a : Mag) : a.bytes.usize.toNat = a.bytes.size := by
  have := maxBytes_lt
  have := a.size_le
  exact USize.toNat_ofNat_of_lt' (by omega)

/-- The digit count, for loops. -/
@[inline, expose] public def usize (a : Mag) : USize := a.bytes.usize >>> 2

public theorem usize_toNat (a : Mag) : a.usize.toNat = a.n := by
  rw [usize, USize.toNat_shiftRight, two_toNat_mod, bytes_usize_toNat, Nat.shiftRight_eq_div_pow]
  rfl

public theorem shiftLeft_toNat (i : USize) (h : i.toNat * 4 < USize.size) :
    (i <<< 2).toNat = i.toNat * 4 := by
  rw [USize.toNat_shiftLeft, two_toNat_mod, Nat.shiftLeft_eq, ← USize.size_eq_two_pow,
    Nat.mod_eq_of_lt (by omega)]

public theorem offset_toNat {a : Mag} {i : USize} (h : i.toNat < a.n) : (i <<< 2).toNat = i.toNat * 4 := by
  have h1 := maxBytes_lt
  have h2 := a.n_le
  exact shiftLeft_toNat i (by omega)

public theorem offset_ok {a : Mag} {i : USize} (h : i.toNat < a.n) :
    (i <<< 2).toNat + 4 ≤ a.bytes.size := by
  rw [offset_toNat h, ← a.n_mul_four]; omega

/-- Digit `i`. -/
@[inline, expose] public def get (a : Mag) (i : USize) (h : i.toNat < a.n) : UInt32 :=
  a.bytes.ugetUInt32LE (i <<< 2) (offset_ok h)

public theorem size_usetUInt32LE (b : ByteArray) (i : USize) (v : UInt32) (h) :
    (b.usetUInt32LE i v h).size = b.size := by
  simp [ByteArray.usetUInt32LE]

/-- Sets digit `i`. -/
@[inline, expose] public def set (a : Mag) (i : USize) (h : i.toNat < a.n) (v : UInt32) : Mag where
  bytes := a.bytes.usetUInt32LE (i <<< 2) v (offset_ok h)
  size_mod := by rw [size_usetUInt32LE]; exact a.size_mod
  size_le := by rw [size_usetUInt32LE]; exact a.size_le

@[simp] public theorem n_set (a : Mag) (i : USize) (h : i.toNat < a.n) (v : UInt32) :
    (a.set i h v).n = a.n := by
  simp [set, n, size_usetUInt32LE]

public theorem size_replicate (k : Nat) (v : UInt8) : (ByteArray.replicate k v).size = k := by
  simp [ByteArray.replicate, ByteArray.size]

/-- `k` zero digits. -/
@[inline, expose] public def zeros (k : USize) (h : k.toNat * 4 ≤ maxBytes) : Mag where
  bytes := ByteArray.replicate (k.toNat * 4) 0
  size_mod := by rw [size_replicate]; omega
  size_le := by rw [size_replicate]; exact h

@[simp] public theorem n_zeros (k : USize) (h) : (zeros k h).n = k.toNat := by
  simp [zeros, n, size_replicate]

/-- The magnitude `0`, allocated on use rather than as a module-level constant. -/
@[inline, expose] public def empty : Mag := ⟨ByteArray.replicate 0 0, by rw [size_replicate], by rw [size_replicate]; exact Nat.zero_le _⟩

public instance : Inhabited Mag := ⟨empty⟩

public theorem size_shrink (b : ByteArray) (k : Nat) : (b.shrink k).size = min k b.size := by
  rw [ByteArray.shrink, ByteArray.size_extract]; omega

/-- The low `k ≤ n` digits. -/
@[inline, expose] public def take (a : Mag) (k : USize) (hk : k.toNat ≤ a.n) : Mag where
  bytes := a.bytes.shrink (k.toNat * 4)
  size_mod := by rw [size_shrink, ← a.n_mul_four]; omega
  size_le := by rw [size_shrink]; have := a.size_le; omega

@[simp] public theorem n_take (a : Mag) (k : USize) (hk) : (a.take k hk).n = k.toNat := by
  have := a.size_mod
  simp only [n] at hk
  simp only [take, n, size_shrink]
  omega

/-- The number of digits below the leading zero digits among the low `k`. -/
@[expose] public def topNonzero (a : Mag) (k : USize) (hk : k.toNat ≤ a.n) : USize :=
  if h : 0 < k.toNat then
    if a.get (k - 1) (by rw [toNat_pred h]; omega) == 0 then
      topNonzero a (k - 1) (by rw [toNat_pred h]; omega)
    else k
  else k
termination_by k.toNat
decreasing_by rw [toNat_pred h]; omega

public theorem topNonzero_le (a : Mag) (k : USize) (hk) : (a.topNonzero k hk).toNat ≤ k.toNat := by
  fun_induction topNonzero a k hk with
  | case1 k hk h _ ih => rw [toNat_pred h] at ih; omega
  | case2 => omega
  | case3 => omega

public theorem usize_le (a : Mag) : a.usize.toNat ≤ a.n := by rw [usize_toNat]; omega

public theorem topNonzero_usize_le (a : Mag) : (a.topNonzero a.usize a.usize_le).toNat ≤ a.n :=
  Nat.le_trans (a.topNonzero_le _ _) a.usize_le

/-- Drops leading zero digits. -/
@[inline, expose] public def normalize (a : Mag) : Mag :=
  a.take (a.topNonzero a.usize a.usize_le) a.topNonzero_usize_le

public theorem usize_succ_toNat (a : Mag) : (a.usize + 1).toNat = a.n + 1 := by
  have := maxBytes_lt; have := a.n_le; have := one_le_maxBytes
  rw [toNat_succ_of_lt_size (by rw [usize_toNat]; omega), usize_toNat]

end Mag

open Mag

/-! ## Comparison -/

/-- Compares the low `i` digits of `a` and `b`, which must both have at least `i` digits. -/
@[expose] public def cmpLoop (a b : Mag) (i : USize) (ha : i.toNat ≤ a.n) (hb : i.toNat ≤ b.n) : Ordering :=
  if h : 0 < i.toNat then
    let x := a.get (i - 1) (by rw [toNat_pred h]; omega)
    let y := b.get (i - 1) (by rw [toNat_pred h]; omega)
    if x != y then (if x < y then .lt else .gt)
    else cmpLoop a b (i - 1) (by rw [toNat_pred h]; omega) (by rw [toNat_pred h]; omega)
  else .eq
termination_by i.toNat
decreasing_by rw [toNat_pred h]; omega

/-- Compares normalized magnitudes. -/
@[expose] public def cmp (a b : Mag) : Ordering :=
  let la := a.usize
  let lb := b.usize
  if h : la = lb then
    cmpLoop a b la a.usize_le (by simp only [la, lb] at h ⊢; rw [h]; exact b.usize_le)
  else if la < lb then .lt else .gt

/-! ## Addition -/

@[expose] public def addTail (a : Mag) (la i : USize) (hla : la.toNat = a.n) (k : UInt64) (c : Mag)
    (hc : a.n < c.n) (hi : i.toNat ≤ la.toNat) : Mag :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 + k
    addTail a la (i+1) hla (t >>> 32) (c.set i (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c.set i (by have := not_lt_toNat h; omega) k.toUInt32
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[expose] public def addLoop (a b : Mag) (la lb i : USize) (hla : la.toNat = a.n) (hlb : lb.toNat = b.n)
    (hab : b.n ≤ a.n) (k : UInt64) (c : Mag) (hc : a.n < c.n) (hi : i.toNat ≤ lb.toNat) : Mag :=
  if h : i < lb then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 + (b.get i (by omega)).toUInt64 + k
    addLoop a b la lb (i+1) hla hlb hab (t >>> 32) (c.set i (by omega) t.toUInt32)
      (by simp; omega) (by rw [toNat_succ_of_lt h]; omega)
  else addTail a la i hla k c hc (by have := not_lt_toNat h; omega)
termination_by lb.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `a + b` for `b.n ≤ a.n`, with `a.n + 1` digits (not normalized). -/
@[expose] public def addCore (a b : Mag) (hab : b.n ≤ a.n) (h : (a.n + 1) * 4 ≤ maxBytes) : Mag :=
  addLoop a b a.usize b.usize 0 (usize_toNat a) (usize_toNat b) hab 0
    (zeros (a.usize + 1) (by rw [usize_succ_toNat]; exact h))
    (by rw [n_zeros, usize_succ_toNat]; omega) (by simp)

/-- `a + b`; panics if the result would exceed `maxBytes`. -/
@[expose] public def add (a b : Mag) : Mag :=
  if hab : b.n ≤ a.n then
    if h : (a.n + 1) * 4 ≤ maxBytes then (addCore a b hab h).normalize else panic! "out of memory"
  else
    if h : (b.n + 1) * 4 ≤ maxBytes then (addCore b a (by omega) h).normalize
    else panic! "out of memory"

/-! ## Subtraction -/

-- Differences are computed in 64 bits, taking the borrow from the sign bit.
@[expose] public def subTail (a : Mag) (la i : USize) (hla : la.toNat = a.n) (k : UInt64) (c : Mag)
    (hc : a.n ≤ c.n) (_hi : i.toNat ≤ la.toNat) : Mag :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 - k
    subTail a la (i+1) hla (t >>> 63) (c.set i (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[expose] public def subLoop (a b : Mag) (la lb i : USize) (hla : la.toNat = a.n) (hlb : lb.toNat = b.n)
    (hab : b.n ≤ a.n) (k : UInt64) (c : Mag) (hc : a.n ≤ c.n) (hi : i.toNat ≤ lb.toNat) : Mag :=
  if h : i < lb then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 - (b.get i (by omega)).toUInt64 - k
    subLoop a b la lb (i+1) hla hlb hab (t >>> 63) (c.set i (by omega) t.toUInt32)
      (by simp; omega) (by rw [toNat_succ_of_lt h]; omega)
  else subTail a la i hla k c hc (by have := not_lt_toNat h; omega)
termination_by lb.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `a - b` for `b.n ≤ a.n` (meaningful for `b ≤ a`), with `a.n` digits (not normalized). -/
@[expose] public def subCore (a b : Mag) (hab : b.n ≤ a.n) : Mag :=
  subLoop a b a.usize b.usize 0 (usize_toNat a) (usize_toNat b) hab 0
    (zeros a.usize (by rw [usize_toNat]; exact a.n_le)) (by rw [n_zeros, usize_toNat]; omega)
    (by simp)

/-- `a - b`, truncated at `0`. -/
@[expose] public def sub (a b : Mag) : Mag :=
  if cmp a b == .lt then empty
  else if hab : b.n ≤ a.n then (subCore a b hab).normalize else empty


/-! ## Multiplication -/

public theorem toNat_add_of_lt_size {i j : USize} (h : i.toNat + j.toNat < USize.size) :
    (i + j).toNat = i.toNat + j.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow, Nat.mod_eq_of_lt h]

public theorem Mag.n_lt_size (c : Mag) : c.n < USize.size := by
  have := c.n_le; have := maxBytes_lt; omega

/-- `c[j..] += a * v`, writing the final carry to `c[j + la]`. -/
@[expose] public def mulInner (a : Mag) (la j : USize) (hla : la.toNat = a.n) (v : UInt64) (i : USize) (k : UInt64)
    (c : Mag) (hc : j.toNat + la.toNat < c.n) (_hi : i.toNat ≤ la.toNat) : Mag :=
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

@[simp] public theorem n_mulInner (a : Mag) (la j hla v i k c hc hi) :
    (mulInner a la j hla v i k c hc hi).n = c.n := by
  fun_induction mulInner a la j hla v i k c hc hi with
  | case1 i k c hc hi h _ _ _ ih => rw [ih]; simp
  | case2 => simp

@[expose] public def mulOuter (a b : Mag) (la lb j : USize) (hla : la.toNat = a.n) (hlb : lb.toNat = b.n)
    (c : Mag) (hc : a.n + b.n ≤ c.n) (_hj : j.toNat ≤ lb.toNat) : Mag :=
  if h : j < lb then
    have hj' := USize.lt_iff_toNat_lt.mp h
    let v := b.get j (by omega)
    mulOuter a b la lb (j+1) hla hlb
      (if v == 0 then c else mulInner a la j hla v.toUInt64 0 0 c (by omega) (by simp))
      (by split <;> simp_all [n_mulInner]) (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by lb.toNat - j.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega


public theorem Mag.usize_add_toNat (a b : Mag) (h : (a.n + b.n) * 4 ≤ maxBytes) :
    (a.usize + b.usize).toNat = a.n + b.n := by
  have := maxBytes_lt
  rw [toNat_add_of_lt_size (by rw [usize_toNat, usize_toNat]; omega), usize_toNat, usize_toNat]

/-- Schoolbook `a * b`, with `a.n + b.n` digits (not normalized). -/
@[expose] public def mulCore (a b : Mag) (h : (a.n + b.n) * 4 ≤ maxBytes) : Mag :=
  mulOuter a b a.usize b.usize 0 (usize_toNat a) (usize_toNat b)
    (zeros (a.usize + b.usize) (by rw [Mag.usize_add_toNat a b h]; exact h))
    (by rw [n_zeros, Mag.usize_add_toNat a b h]; omega) (by simp)

/-- Schoolbook multiplication; panics if the result would exceed `maxBytes`. -/
@[expose] public def mulBasecase (a b : Mag) : Mag :=
  if h : (a.n + b.n) * 4 ≤ maxBytes then
    -- the longer operand goes into the inner loop
    if b.n ≤ a.n then (mulCore a b h).normalize else (mulCore b a (by omega)).normalize
  else panic! "out of memory"


/-! ## Shifts -/

/-- `c[q + i] := a[i]` for `i < la`. -/
@[expose] public def copyLoop (a : Mag) (la q i : USize) (hla : la.toNat = a.n) (c : Mag)
    (hc : q.toNat + la.toNat ≤ c.n) (_hi : i.toNat ≤ la.toNat) : Mag :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    have hqi : (q + i).toNat = q.toNat + i.toNat := toNat_add_of_lt_size (by
      have := c.n_lt_size; omega)
    copyLoop a la q (i+1) hla (c.set (q + i) (by omega) (a.get i (by omega))) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `c[q + i] := a[i] << s | a[i-1] >> (32 - s)` for `i ≤ la`, for `0 < s < 32`. -/
@[expose] public def shlLoop (a : Mag) (la q : USize) (s : UInt32) (i : USize) (hla : la.toNat = a.n) (prev : UInt32)
    (c : Mag) (hc : q.toNat + la.toNat < c.n) (_hi : i.toNat ≤ la.toNat) : Mag :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    have hqi : (q + i).toNat = q.toNat + i.toNat := toNat_add_of_lt_size (by
      have := c.n_lt_size; omega)
    let x := a.get i (by omega)
    shlLoop a la q s (i+1) hla x (c.set (q + i) (by omega) ((x <<< s) ||| (prev >>> (32 - s))))
      (by simp; omega) (by rw [toNat_succ_of_lt h]; omega)
  else
    have hql : (q + la).toNat = q.toNat + la.toNat := toNat_add_of_lt_size (by
      have := c.n_lt_size; omega)
    c.set (q + la) (by omega) (prev >>> (32 - s))
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `a * 2^sh`; panics if the result would exceed `maxBytes`. -/
@[expose] public def shiftLeft (a : Mag) (sh : USize) : Mag :=
  let q := sh >>> 5
  let s := (sh &&& 31).toUInt32
  if h : (a.n + q.toNat + 1) * 4 ≤ maxBytes then
    have hq : (a.usize + q + 1).toNat = a.n + q.toNat + 1 := by
      have := maxBytes_lt
      have h1 : (a.usize + q).toNat = a.n + q.toNat := by
        rw [toNat_add_of_lt_size (by rw [usize_toNat]; omega), usize_toNat]
      rw [toNat_succ_of_lt_size (by rw [h1]; omega), h1]
    let c := zeros (a.usize + q + 1) (by rw [hq]; exact h)
    have hc : c.n = a.n + q.toNat + 1 := by simp only [c, n_zeros, hq]
    (if s == 0 then copyLoop a a.usize q 0 (usize_toNat a) c (by rw [hc, usize_toNat]; omega) (by simp)
     else shlLoop a a.usize q s 0 (usize_toNat a) 0 c (by rw [hc, usize_toNat]; omega) (by simp)).normalize
  else panic! "out of memory"


/-- `c[i] := a[q + i]` for `i < n`. -/
@[expose] public def copyDown (a : Mag) (q n : USize) (hqn : q.toNat + n.toNat ≤ a.n) (i : USize) (c : Mag)
    (hc : n.toNat ≤ c.n) (_hi : i.toNat ≤ n.toNat) : Mag :=
  if h : i < n then
    have hi' := USize.lt_iff_toNat_lt.mp h
    have hqi : (q + i).toNat = q.toNat + i.toNat := toNat_add_of_lt_size (by
      have := a.n_lt_size; omega)
    copyDown a q n hqn (i+1) (c.set i (by omega) (a.get (q + i) (by omega))) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by n.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `c[i] := a[q + i] >> s | a[q + i + 1] << (32 - s)` for `i < n`, where `q + n = a.n` and digits
past the end are `0`, for `0 < s < 32`. -/
@[expose] public def shrLoop (a : Mag) (q n : USize) (s : UInt32) (hqn : q.toNat + n.toNat = a.n) (i : USize) (c : Mag)
    (hc : n.toNat ≤ c.n) (_hi : i.toNat ≤ n.toNat) : Mag :=
  if h : i < n then
    have hi' := USize.lt_iff_toNat_lt.mp h
    have hqi : (q + i).toNat = q.toNat + i.toNat := toNat_add_of_lt_size (by
      have := a.n_lt_size; omega)
    let x := a.get (q + i) (by omega)
    let y := if h2 : i + 1 < n then
        have hqi1 : (q + i + 1).toNat = q.toNat + i.toNat + 1 := by
          rw [toNat_succ_of_lt_size (by have := a.n_lt_size; omega), hqi]
        have := USize.lt_iff_toNat_lt.mp h2
        a.get (q + i + 1) (by rw [toNat_succ_of_lt h] at this; omega)
      else 0
    shrLoop a q n s hqn (i+1) (c.set i (by omega) ((x >>> s) ||| (y <<< (32 - s)))) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by n.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `a / 2^sh`. -/
@[expose] public def shiftRight (a : Mag) (sh : USize) : Mag :=
  let q := sh >>> 5
  let s := (sh &&& 31).toUInt32
  if h : q.toNat < a.n then
    let n := a.usize - q
    have hn : n.toNat = a.n - q.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [usize_toNat]; omega)),
        usize_toNat]
    let c := zeros n (by rw [hn]; have := a.n_le; omega)
    have hc : c.n = n.toNat := n_zeros _ _
    (if s == 0 then copyDown a q n (by rw [hn]; omega) 0 c (by omega) (by simp)
     else shrLoop a q n s (by rw [hn]; omega) 0 c (by omega) (by simp)).normalize
  else empty


@[inline, expose] public def getOr0 (a : Mag) (i : USize) : UInt32 :=
  if h : i < a.usize then a.get i (by rw [← usize_toNat]; exact USize.lt_iff_toNat_lt.mp h) else 0

/-- `c[i] := f a[i] b[i]` for `i < n`, reading digits past the end as `0`. -/
@[specialize, expose] public def zipLoop (f : UInt32 → UInt32 → UInt32) (a b : Mag) (n i : USize) (c : Mag)
    (hc : n.toNat ≤ c.n) (_hi : i.toNat ≤ n.toNat) : Mag :=
  if h : i < n then
    have hi' := USize.lt_iff_toNat_lt.mp h
    zipLoop f a b n (i+1) (c.set i (by omega) (f (getOr0 a i) (getOr0 b i))) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by n.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[inline, expose] public def zipWith (f : UInt32 → UInt32 → UInt32) (a b : Mag) (n : USize)
    (hn : n.toNat ≤ max a.n b.n) : Mag :=
  zipLoop f a b n 0 (zeros n (by have := a.n_le; have := b.n_le; omega)) (by simp) (by simp)

@[expose] public def land (a b : Mag) : Mag :=
  (zipWith (· &&& ·) a b (if a.usize ≤ b.usize then a.usize else b.usize) (by
    split <;> simp only [usize_toNat] <;> omega)).normalize

@[expose] public def lor (a b : Mag) : Mag :=
  zipWith (· ||| ·) a b (if a.usize ≤ b.usize then b.usize else a.usize) (by
    split <;> simp only [usize_toNat] <;> omega)

@[expose] public def xor (a b : Mag) : Mag :=
  (zipWith (· ^^^ ·) a b (if a.usize ≤ b.usize then b.usize else a.usize) (by
    split <;> simp only [usize_toNat] <;> omega)).normalize


/-! ## Single-digit operations -/

@[expose] public def mulAddSmallLoop (a : Mag) (la : USize) (hla : la.toNat = a.n) (m : UInt64) (i : USize) (k : UInt64)
    (c : Mag) (hc : la.toNat < c.n) (_hi : i.toNat ≤ la.toNat) : Mag :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 * m + k
    mulAddSmallLoop a la hla m (i+1) (t >>> 32) (c.set i (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c.set la (by omega) k.toUInt32
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `a * m + k`. -/
@[expose] public def mulAddSmall (a : Mag) (m k : UInt32) : Mag :=
  if h : (a.n + 1) * 4 ≤ maxBytes then
    (mulAddSmallLoop a a.usize a.usize_toNat m.toUInt64 0 k.toUInt64
      (zeros (a.usize + 1) (by rw [a.usize_succ_toNat]; exact h))
      (by rw [n_zeros, a.usize_succ_toNat, a.usize_toNat]; omega) (by simp)).normalize
  else panic! "out of memory"

@[expose] public def div1Loop (a : Mag) (d : UInt64) (j : USize) (hj : j.toNat ≤ a.n) (r : UInt64) (q : Mag)
    (hq : j.toNat ≤ q.n) : Mag × UInt64 :=
  if h : 0 < j then
    have hj0 : 0 < j.toNat := USize.lt_iff_toNat_lt.mp h
    have hp := toNat_pred hj0
    let t := (r <<< 32) ||| (a.get (j - 1) (by omega)).toUInt64
    div1Loop a d (j - 1) (by omega) (t % d) (q.set (j - 1) (by omega) (t / d).toUInt32)
      (by simp; omega)
  else (q, r)
termination_by j.toNat
decreasing_by rw [hp]; omega

/-- Quotient and remainder by a nonzero single digit `d`. -/
@[expose] public def divModSmall (a : Mag) (d : UInt32) : Mag × UInt32 :=
  let p := div1Loop a d.toUInt64 a.usize a.usize_le 0 (zeros a.usize (by
    rw [a.usize_toNat]; exact a.n_le)) (by rw [n_zeros]; exact Nat.le_refl _)
  (p.1.normalize, p.2.toUInt32)


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


public theorem two_usize_toNat : (2 : USize).toNat = 2 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h]

public theorem toNat_sub_two {i : USize} (h : 2 ≤ i.toNat) : (i - 2).toNat = i.toNat - 2 := by
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [two_usize_toNat]; omega)),
    two_usize_toNat]

public theorem eight_le_maxBytes : 8 ≤ maxBytes := by
  rcases System.Platform.numBits_eq with h | h <;> simp [maxBytes, h]

@[expose] public def ofUInt64 (x : UInt64) : Mag :=
  have h2 := two_usize_toNat
  (((zeros 2 (by rw [h2]; have := eight_le_maxBytes; omega)).set 0 (by simp [h2]) x.toUInt32).set 1
    (by simp [h2]) (x >>> 32).toUInt32).normalize

@[simp] public theorem n_copyLoop (a la q i hla c hc hi) : (copyLoop a la q i hla c hc hi).n = c.n := by
  fun_induction copyLoop a la q i hla c hc hi <;> simp_all

@[simp] public theorem n_shlLoop (a la q s i hla prev c hc hi) :
    (shlLoop a la q s i hla prev c hc hi).n = c.n := by
  fun_induction shlLoop a la q s i hla prev c hc hi <;> simp_all

@[simp] public theorem n_shrLoop (a q n s hqn i c hc hi) : (shrLoop a q n s hqn i c hc hi).n = c.n := by
  fun_induction shrLoop a q n s hqn i c hc hi <;> simp_all

/-- `ms[0..n] := q * v[0..n)`. -/
@[expose] public def mul1Loop (q : UInt64) (v : Mag) (n : USize) (hn : n.toNat ≤ v.n) (i : USize) (k : UInt64)
    (ms : Mag) (hms : n.toNat < ms.n) (_hi : i.toNat ≤ n.toNat) : Mag :=
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
@[expose] public def subInPlace (b : Mag) (len off : USize) (hb : len.toNat ≤ b.n) (i : USize) (k : UInt64) (u : Mag)
    (hu : off.toNat + len.toNat ≤ u.n) (_hi : i.toNat ≤ len.toNat) : Mag :=
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
@[expose] public def addInPlace (v : Mag) (len off : USize) (i : USize) (k : UInt64) (u : Mag)
    (hu : off.toNat + len.toNat ≤ u.n) (_hi : i.toNat ≤ len.toNat) : Mag :=
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
@[expose] public def divNLoop (v : Mag) (n : USize) (hn2 : 2 ≤ n.toNat) (hnv : n.toNat ≤ v.n) (vtop vsec : UInt64)
    (j1 : USize) (q u ms : Mag) (hq : j1.toNat ≤ q.n) (hu : j1.toNat + n.toNat ≤ u.n)
    (hms : n.toNat < ms.n) : Mag × Mag :=
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
@[inline, expose] public def shiftDivisor (b : Mag) (lb : USize) (hlb : lb.toNat = b.n) (s : UInt32)
    (h : (lb.toNat + 1) * 4 ≤ maxBytes) : {v : Mag // lb.toNat ≤ v.n} :=
  have hlb1 : (lb + 1).toNat = lb.toNat + 1 := toNat_succ_of_lt_size (by have := maxBytes_lt; omega)
  if s == 0 then ⟨b, by omega⟩
  else ⟨shlLoop b lb 0 s 0 hlb 0 (zeros (lb + 1) (by omega))
      (by simp only [n_zeros, USize.toNat_zero, Nat.zero_add]; omega) (by simp),
    by simp only [n_zeros, n_shlLoop]; omega⟩

/-- The dividend shifted left by `s < 32`, with one more digit. -/
@[inline, expose] public def shiftDividend (a : Mag) (la : USize) (hla : la.toNat = a.n) (s : UInt32)
    (h : (la.toNat + 1) * 4 ≤ maxBytes) : {u : Mag // u.n = la.toNat + 1} :=
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
@[inline, expose] public def knuthRem (u : Mag) (lb : USize) (hlb : lb.toNat ≤ u.n) (s : UInt32)
    (h : lb.toNat * 4 ≤ maxBytes) : Mag :=
  if s == 0 then u.take lb hlb
  else shrLoop (u.take lb hlb) 0 lb s (by simp) 0 (zeros lb h) (by simp) (by simp)

/-- Algorithm D on the operands `v` and `u`, already shifted left by `s`. -/
@[inline, expose] public def knuthCore (a b : Mag) (h : 2 ≤ b.n ∧ b.n ≤ a.n ∧ (a.n + 1) * 4 ≤ maxBytes) (s : UInt32)
    (v : {v : Mag // b.usize.toNat ≤ v.n}) (u : {u : Mag // u.n = a.usize.toNat + 1}) : Mag × Mag :=
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
@[expose] public def knuth (a b : Mag) (h : 2 ≤ b.n ∧ b.n ≤ a.n ∧ (a.n + 1) * 4 ≤ maxBytes) : Mag × Mag :=
  have hlb : b.usize.toNat = b.n := b.usize_toNat
  have hla : a.usize.toNat = a.n := a.usize_toNat
  have hlb1 : (b.usize - 1).toNat = b.usize.toNat - 1 := toNat_pred (by omega)
  -- normalize so that the top digit of the divisor has its high bit set
  let s := 31 - (b.get (b.usize - 1) (by omega)).log2
  knuthCore a b h s (shiftDivisor b b.usize hlb s (by omega)) (shiftDividend a a.usize hla s (by omega))

/-- Quotient and remainder by long division; `b = 0` gives `(0, a)`. -/
@[expose] public def divModBasecase (a b : Mag) : Mag × Mag :=
  if cmp a b == .lt then (empty, a)
  else if h1 : b.usize = 1 then
    let p := divModSmall a (b.get 0 (by have := b.usize_toNat; rw [h1] at this; simp at this ⊢; omega))
    (p.1, ofUInt64 p.2.toUInt64)
  else if h : 2 ≤ b.n ∧ b.n ≤ a.n then
    if h' : (a.n + 1) * 4 ≤ maxBytes then knuth a b ⟨h.1, h.2, h'⟩ else panic! "out of memory"
  else (empty, a)


/-! ## Karatsuba multiplication -/

public theorem n_normalize_le (a : Mag) : a.normalize.n ≤ a.n := by
  have := a.topNonzero_le a.usize a.usize_le
  simp only [normalize, n_take]
  rw [a.usize_toNat] at this
  exact this

public theorem n_panic (msg : String) : (panic msg : Mag).n = 0 := by unfold panic panicCore; rfl

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

public theorem n_add_le (a b : Mag) : (add a b).n ≤ max a.n b.n + 1 := by
  unfold add
  split
  · split
    · have := n_normalize_le (addCore a b ‹_› ‹_›); rw [n_addCore] at this; omega
    · simp [panicWithPosWithDecl, n_panic]
  · split
    · have := n_normalize_le (addCore b a (by omega) ‹_›); rw [n_addCore] at this; omega
    · simp [panicWithPosWithDecl, n_panic]

/-- Digits `[lo, hi)` of `a` for `lo ≤ hi ≤ a.n`. -/
@[inline, expose] public def extractDigits (a : Mag) (lo hi : USize) (h1 : lo.toNat ≤ hi.toNat) (h2 : hi.toNat ≤ a.n) :
    Mag where
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

@[simp] public theorem n_extractDigits (a : Mag) (lo hi h1 h2) :
    (extractDigits a lo hi h1 h2).n = hi.toNat - lo.toNat := by
  have := maxBytes_lt; have := a.n_le
  have h := (extractDigits a lo hi h1 h2).n_mul_four
  have hs : (extractDigits a lo hi h1 h2).bytes.size = min (hi.toNat * 4) (a.n * 4) - lo.toNat * 4 := by
    simp only [extractDigits, ByteArray.size_extract, shiftLeft_toNat lo (by omega),
      shiftLeft_toNat hi (by omega), ← a.n_mul_four]
  omega

/-- `min hi a.usize`. -/
@[inline, expose] public def clampHi (a : Mag) (hi : USize) : {h : USize // h.toNat = min hi.toNat a.n} :=
  if h : hi ≤ a.usize then
    ⟨hi, by have := USize.le_iff_toNat_le.mp h; rw [a.usize_toNat] at this; omega⟩
  else ⟨a.usize, by have := not_le_toNat h; rw [a.usize_toNat] at this ⊢; omega⟩

/-- Digits `[lo, min hi a.n)` of `a`, normalized. -/
@[expose] public def slice (a : Mag) (lo hi : USize) : Mag :=
  let hi' := clampHi a hi
  if h : hi'.1 ≤ lo then empty
  else (extractDigits a lo hi'.1 (by have := not_le_toNat h; omega) (by rw [hi'.2]; omega)).normalize

public theorem n_slice_le (a : Mag) (lo hi : USize) :
    (slice a lo hi).n ≤ hi.toNat - lo.toNat ∧ (slice a lo hi).n ≤ a.n - lo.toNat := by
  have hc := (clampHi a hi).2
  unfold slice
  dsimp only
  split
  · have : (empty : Mag).n = 0 := rfl
    omega
  · next h =>
    have h1 := n_normalize_le (extractDigits a lo (clampHi a hi).1 (by have := not_le_toNat h; omega)
      (by rw [hc]; omega))
    rw [n_extractDigits] at h1
    omega

/-- `a * 2^(32 k)`; panics if the result would exceed `maxBytes`. -/
@[inline, expose] public def shiftDigits (a : Mag) (k : USize) : Mag :=
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
@[expose] public def mul (a b : Mag) : Mag :=
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


/-! ## Newton division -/

@[inline, expose] public def bitLen (a : Mag) : USize :=
  let n := a.usize
  if h : n = 0 then 0
  else
    have hn : 0 < n.toNat := by
      have : n.toNat ≠ 0 := fun h' => h (USize.toNat_inj.mp (by simpa using h'))
      omega
    ((n - 1) <<< 5) + (a.get (n - 1) (by rw [toNat_pred hn, a.usize_toNat] at *; omega)).log2.toUSize + 1

@[inline, expose] public def pow2 (k : USize) : Mag := shiftLeft (ofUInt64 1) k

/--
Approximates `2^(m + L) / b`, where `m` is the bit length of `b`, by Newton iteration, using only the
top `L + 64` bits of `b`. Division only relies on the result through checked corrections.
-/
@[expose] public def recip (b : Mag) (L : USize) : Mag :=
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
@[expose] public def newtonDown (a b : Mag) (fuel : Nat) (q qb : Mag) : Mag × Mag :=
  let q := sub q (ofUInt64 1)
  let qb := sub qb b
  if cmp qb a == .gt then
    match fuel with
    | 0 => divModBasecase a b
    | fuel + 1 => newtonDown a b fuel q qb
  else (q, sub a qb)

/-- Steps the quotient estimate `q` (with `q * b + r = a`) up. -/
@[expose] public def newtonUp (a b : Mag) (fuel : Nat) (q r : Mag) : Mag × Mag :=
  if cmp r b != .lt then
    match fuel with
    | 0 => divModBasecase a b
    | fuel + 1 => newtonUp a b fuel (add q (ofUInt64 1)) (sub r b)
  else (q, r)

/--
Corrects the quotient estimate `q` to the exact quotient and remainder. The size check, which a
good estimate always passes, keeps `mul q b` from overflowing.
-/
@[inline, expose] public def newtonFinish (a b q : Mag) : Mag × Mag :=
  if q.n + b.n ≤ a.n + 2 then
    let qb := mul q b
    if cmp qb a == .gt then newtonDown a b 64 q qb else newtonUp a b 64 q (sub a qb)
  else divModBasecase a b

/-- Quotient and remainder by `b ≠ 0` via a Newton reciprocal, for `b ≤ a`. -/
@[expose] public def divModNewton (a b : Mag) : Mag × Mag :=
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
@[expose] public def divMod (a b : Mag) : Mag × Mag :=
  let m := bitLen b
  let n := bitLen a
  if m ≥ 24576 && n ≥ m + 24576 then divModNewton a b else divModBasecase a b


/-! ## Bit queries -/

/-- `⌊log₂ a⌋` for `a ≠ 0`, and `0` for `a = 0`. -/
@[expose] public def log2 (a : Mag) : USize :=
  let n := a.usize
  if h : n = 0 then 0
  else
    have hn : 0 < n.toNat := by
      have : n.toNat ≠ 0 := fun h' => h (USize.toNat_inj.mp (by simpa using h'))
      omega
    ((n - 1) <<< 5) + (a.get (n - 1) (by rw [toNat_pred hn, a.usize_toNat] at *; omega)).log2.toUSize

/-- The number of trailing zero bits of `x`, plus `i`, for `x ≠ 0`. -/
@[expose] public def ctz32 (x : UInt32) (i : USize) (hi : i.toNat ≤ 32) : USize :=
  if h : i < 32 ∧ x &&& 1 = 0 then
    have : i.toNat < 32 := by
      have h1 := USize.lt_iff_toNat_lt.mp h.1
      have e32 : (32 : USize).toNat = 32 := by
        rcases System.Platform.numBits_eq with e | e <;> simp [USize.toNat_ofNat, e]
      omega
    have : 32 < USize.size := by
      rcases System.Platform.numBits_eq with e | e <;> simp [USize.size, e]
    ctz32 (x >>> 1) (i + 1) (by rw [toNat_succ_of_lt_size (by omega)]; omega)
  else i
termination_by 32 - i.toNat
decreasing_by
  rw [toNat_succ_of_lt_size (by omega)]; omega

@[expose] public def trailingZerosLoop (a : Mag) (i : USize) (_hi : i.toNat ≤ a.n) : USize :=
  if h : i < a.usize then
    have hi' : i.toNat < a.n := by have := USize.lt_iff_toNat_lt.mp h; rw [a.usize_toNat] at this; exact this
    let x := a.get i hi'
    if x == 0 then
      trailingZerosLoop a (i + 1) (by rw [toNat_succ_of_lt_size (by have := a.n_lt_size; omega)]; omega)
    else (i <<< 5) + ctz32 x 0 (by simp)
  else 0
termination_by a.n - i.toNat
decreasing_by rw [toNat_succ_of_lt_size (by have := a.n_lt_size; omega)]; omega

/-- The number of trailing zero bits of `a ≠ 0`, and `0` for `a = 0`. -/
@[expose] public def trailingZeros (a : Mag) : USize := trailingZerosLoop a 0 (by simp)

/-- The value modulo `2^64`. -/
@[expose] public def low64 (a : Mag) : UInt64 :=
  (getOr0 a 0).toUInt64 ||| (getOr0 a 1).toUInt64 <<< 32


/-! ## Powers -/

@[expose] public def powLoop (base : Mag) (e : USize) (acc : Mag) : Mag :=
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

@[expose] public def pow (a : Mag) (e : USize) : Mag := powLoop a e (ofUInt64 1)

/-! ## Greatest common divisor -/

/--
Euclid's algorithm with a step budget. Two steps at least halve the remainder, so the budget of
`gcd` always suffices for normalized inputs.
-/
@[expose] public def gcdLoop : Nat → Mag → Mag → Mag
  | 0, a, _ => a
  | fuel + 1, a, b => if b.usize == 0 then a else gcdLoop fuel b (divMod a b).2

@[expose] public def gcd (a b : Mag) : Mag := gcdLoop (64 * (a.n + b.n) + 2) a b

/-! ## Modular powers -/

@[expose] public def powModLoop (e m : Mag) (nbits i : USize) (base acc : Mag) : Mag :=
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
@[expose] public def powMod (a e m : Mag) : Mag :=
  if e.usize == 0 then ofUInt64 1
  else powModLoop e m (log2 e + 1) 0 (divMod a m).2 (ofUInt64 1)

/-! ## Parsing -/

public structure DecimalState where
  acc : Mag
  chunk : UInt32
  ndig : UInt32

@[expose] public def ofDecimalStep (st : DecimalState) (c : UInt8) : DecimalState :=
  if '0'.toUInt8 ≤ c && c ≤ '9'.toUInt8 then
    let chunk := st.chunk * 10 + (c - '0'.toUInt8).toUInt32
    if st.ndig + 1 == 9 then ⟨mulAddSmall st.acc 1000000000 chunk, 0, 0⟩
    else ⟨st.acc, chunk, st.ndig + 1⟩
  else st

@[expose] public def ofDecimalLoop (b : ByteArray) (i : Nat) (st : DecimalState) : DecimalState :=
  if h : i < b.size then ofDecimalLoop b (i + 1) (ofDecimalStep st b[i]) else st
termination_by b.size - i

@[expose] public def pow10 (n acc : UInt32) : UInt32 := if h : n = 0 then acc else pow10 (n - 1) (acc * 10)
termination_by n.toNat
decreasing_by
  have : n.toNat ≠ 0 := fun h' => h (UInt32.toNat_inj.mp (by simpa using h'))
  rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-- Parses the decimal digits of `s`, ignoring all other characters. -/
@[expose] public def ofDecimal (s : String) : Mag :=
  let st := ofDecimalLoop s.toUTF8 0 ⟨Mag.empty, 0, 0⟩
  mulAddSmall st.acc (pow10 st.ndig 1) st.chunk

/-! ## Printing -/

/--
The base-`10^9` digits of `a`, least significant first. Each step removes at least 29 bits, so a
budget of `2 * a.n` steps always suffices.
-/
@[expose] public def chunksLoop : Nat → Mag → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | fuel + 1, a, acc =>
    if a.usize == 0 then acc else
      let p := divModSmall a 1000000000
      chunksLoop fuel p.1 (acc.push p.2)

/-- The decimal representation of `a`. -/
@[expose] public def toDecimal (a : Mag) : String :=
  let chunks := chunksLoop (2 * a.n) a #[]
  if chunks.isEmpty then "0" else
    let top := toString chunks.back!
    chunks.pop.foldr (init := top) fun c s =>
      let d := toString c
      s ++ "".pushn '0' (9 - d.length) ++ d

end Nat.Big
