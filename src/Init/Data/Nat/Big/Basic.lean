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
# Big natural numbers: representation and basic operations

The `BigNat` type, comparison, addition, subtraction, shifts, bitwise operations, single-digit
operations, bit queries, and decimal parsing and printing. See `Init.Data.Nat.Big` for the
representation and the constraints on these definitions.
-/

set_option compiler.extract_closed false

namespace Nat.Big


/--
The largest byte size of a `BigNat`, `2 ^ (System.Platform.numBits - 4)`, far below `USize.size`.
Both values fit in a scalar on their platform, so evaluating `maxBytes` never creates a big `Nat`,
which would call back into this module.
-/
@[inline, expose] public def maxBytes : Nat :=
  if System.Platform.numBits = 64 then 2 ^ 60 else 2 ^ 28

public theorem maxBytes_eq : maxBytes = 2 ^ (System.Platform.numBits - 4) := by
  rcases System.Platform.numBits_eq with h | h <;> simp [maxBytes, h]

public theorem maxBytes_lt : maxBytes * 8 < USize.size := by
  have : USize.size = 2 ^ System.Platform.numBits := rfl
  rcases System.Platform.numBits_eq with h | h <;> simp [maxBytes, this, h]

public theorem one_le_maxBytes : 1 ≤ maxBytes := by rw [maxBytes_eq]; exact Nat.one_le_two_pow

public structure BigNat where
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

namespace BigNat

/-- The number of digits. -/
@[expose] public def n (a : BigNat) : Nat := a.bytes.size / 4

public theorem n_mul_four (a : BigNat) : a.n * 4 = a.bytes.size := by
  have := a.size_mod; simp only [n]; omega

public theorem n_le (a : BigNat) : a.n * 4 ≤ maxBytes := by rw [n_mul_four]; exact a.size_le

public theorem two_toNat_mod : (2 : USize).toNat % System.Platform.numBits = 2 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

public theorem bytes_usize_toNat (a : BigNat) : a.bytes.usize.toNat = a.bytes.size := by
  have := maxBytes_lt
  have := a.size_le
  exact USize.toNat_ofNat_of_lt' (by omega)

/-- The digit count, for loops. -/
@[inline, expose] public def usize (a : BigNat) : USize := a.bytes.usize >>> 2

public theorem usize_toNat (a : BigNat) : a.usize.toNat = a.n := by
  rw [usize, USize.toNat_shiftRight, two_toNat_mod, bytes_usize_toNat, Nat.shiftRight_eq_div_pow]
  rfl

public theorem shiftLeft_toNat (i : USize) (h : i.toNat * 4 < USize.size) :
    (i <<< 2).toNat = i.toNat * 4 := by
  rw [USize.toNat_shiftLeft, two_toNat_mod, Nat.shiftLeft_eq, ← USize.size_eq_two_pow,
    Nat.mod_eq_of_lt (by omega)]

public theorem offset_toNat {a : BigNat} {i : USize} (h : i.toNat < a.n) : (i <<< 2).toNat = i.toNat * 4 := by
  have h1 := maxBytes_lt
  have h2 := a.n_le
  exact shiftLeft_toNat i (by omega)

public theorem offset_ok {a : BigNat} {i : USize} (h : i.toNat < a.n) :
    (i <<< 2).toNat + 4 ≤ a.bytes.size := by
  rw [offset_toNat h, ← a.n_mul_four]; omega

/-- Digit `i`. -/
@[inline, expose] public def get (a : BigNat) (i : USize) (h : i.toNat < a.n) : UInt32 :=
  a.bytes.ugetUInt32LE (i <<< 2) (offset_ok h)

public theorem size_usetUInt32LE (b : ByteArray) (i : USize) (v : UInt32) (h) :
    (b.usetUInt32LE i v h).size = b.size := by
  simp [ByteArray.usetUInt32LE]

/-- Sets digit `i`. -/
@[inline, expose] public def set (a : BigNat) (i : USize) (h : i.toNat < a.n) (v : UInt32) : BigNat where
  bytes := a.bytes.usetUInt32LE (i <<< 2) v (offset_ok h)
  size_mod := by rw [size_usetUInt32LE]; exact a.size_mod
  size_le := by rw [size_usetUInt32LE]; exact a.size_le

@[simp] public theorem n_set (a : BigNat) (i : USize) (h : i.toNat < a.n) (v : UInt32) :
    (a.set i h v).n = a.n := by
  simp [set, n, size_usetUInt32LE]

public theorem size_replicate (k : Nat) (v : UInt8) : (ByteArray.replicate k v).size = k := by
  simp [ByteArray.replicate, ByteArray.size]

/-- `k` zero digits. -/
@[inline, expose] public def zeros (k : USize) (h : k.toNat * 4 ≤ maxBytes) : BigNat where
  bytes := ByteArray.replicate (k.toNat * 4) 0
  size_mod := by rw [size_replicate]; omega
  size_le := by rw [size_replicate]; exact h

@[simp] public theorem n_zeros (k : USize) (h) : (zeros k h).n = k.toNat := by
  simp [zeros, n, size_replicate]

/-- The `BigNat` `0`, allocated on use rather than as a module-level constant. -/
@[inline, expose] public def empty : BigNat := ⟨ByteArray.replicate 0 0, by rw [size_replicate], by rw [size_replicate]; exact Nat.zero_le _⟩

public instance : Inhabited BigNat := ⟨empty⟩

public theorem size_shrink (b : ByteArray) (k : Nat) : (b.shrink k).size = min k b.size := by
  rw [ByteArray.shrink, ByteArray.size_extract]; omega

/-- The low `k ≤ n` digits. -/
@[inline, expose] public def take (a : BigNat) (k : USize) (hk : k.toNat ≤ a.n) : BigNat where
  bytes := a.bytes.shrink (k.toNat * 4)
  size_mod := by rw [size_shrink, ← a.n_mul_four]; omega
  size_le := by rw [size_shrink]; have := a.size_le; omega

@[simp] public theorem n_take (a : BigNat) (k : USize) (hk) : (a.take k hk).n = k.toNat := by
  have := a.size_mod
  simp only [n] at hk
  simp only [take, n, size_shrink]
  omega

/-- The number of digits below the leading zero digits among the low `k`. -/
@[expose] public def topNonzero (a : BigNat) (k : USize) (hk : k.toNat ≤ a.n) : USize :=
  if h : 0 < k.toNat then
    if a.get (k - 1) (by rw [toNat_pred h]; omega) == 0 then
      topNonzero a (k - 1) (by rw [toNat_pred h]; omega)
    else k
  else k
termination_by k.toNat
decreasing_by rw [toNat_pred h]; omega

public theorem topNonzero_le (a : BigNat) (k : USize) (hk) : (a.topNonzero k hk).toNat ≤ k.toNat := by
  fun_induction topNonzero a k hk with
  | case1 k hk h _ ih => rw [toNat_pred h] at ih; omega
  | case2 => omega
  | case3 => omega

public theorem usize_le (a : BigNat) : a.usize.toNat ≤ a.n := by rw [usize_toNat]; omega

public theorem topNonzero_usize_le (a : BigNat) : (a.topNonzero a.usize a.usize_le).toNat ≤ a.n :=
  Nat.le_trans (a.topNonzero_le _ _) a.usize_le

/-- Drops leading zero digits. -/
@[inline, expose] public def normalize (a : BigNat) : BigNat :=
  a.take (a.topNonzero a.usize a.usize_le) a.topNonzero_usize_le

public theorem usize_succ_toNat (a : BigNat) : (a.usize + 1).toNat = a.n + 1 := by
  have := maxBytes_lt; have := a.n_le; have := one_le_maxBytes
  rw [toNat_succ_of_lt_size (by rw [usize_toNat]; omega), usize_toNat]

end BigNat

open BigNat

/-! ## Comparison -/

/-- Compares the low `i` digits of `a` and `b`, which must both have at least `i` digits. -/
@[expose] public def cmpLoop (a b : BigNat) (i : USize) (ha : i.toNat ≤ a.n) (hb : i.toNat ≤ b.n) : Ordering :=
  if h : 0 < i.toNat then
    let x := a.get (i - 1) (by rw [toNat_pred h]; omega)
    let y := b.get (i - 1) (by rw [toNat_pred h]; omega)
    if x != y then (if x < y then .lt else .gt)
    else cmpLoop a b (i - 1) (by rw [toNat_pred h]; omega) (by rw [toNat_pred h]; omega)
  else .eq
termination_by i.toNat
decreasing_by rw [toNat_pred h]; omega

/-- Compares normalized `BigNat`s. -/
@[expose] public def cmp (a b : BigNat) : Ordering :=
  let la := a.usize
  let lb := b.usize
  if h : la = lb then
    cmpLoop a b la a.usize_le (by simp only [la, lb] at h ⊢; rw [h]; exact b.usize_le)
  else if la < lb then .lt else .gt

/-! ## Addition -/

@[expose] public def addTail (a : BigNat) (la i : USize) (hla : la.toNat = a.n) (k : UInt64) (c : BigNat)
    (hc : a.n < c.n) (hi : i.toNat ≤ la.toNat) : BigNat :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 + k
    addTail a la (i+1) hla (t >>> 32) (c.set i (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c.set i (by have := not_lt_toNat h; omega) k.toUInt32
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[expose] public def addLoop (a b : BigNat) (la lb i : USize) (hla : la.toNat = a.n) (hlb : lb.toNat = b.n)
    (hab : b.n ≤ a.n) (k : UInt64) (c : BigNat) (hc : a.n < c.n) (hi : i.toNat ≤ lb.toNat) : BigNat :=
  if h : i < lb then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 + (b.get i (by omega)).toUInt64 + k
    addLoop a b la lb (i+1) hla hlb hab (t >>> 32) (c.set i (by omega) t.toUInt32)
      (by simp; omega) (by rw [toNat_succ_of_lt h]; omega)
  else addTail a la i hla k c hc (by have := not_lt_toNat h; omega)
termination_by lb.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `a + b` for `b.n ≤ a.n`, with `a.n + 1` digits (not normalized). -/
@[expose] public def addCore (a b : BigNat) (hab : b.n ≤ a.n) (h : (a.n + 1) * 4 ≤ maxBytes) : BigNat :=
  addLoop a b a.usize b.usize 0 (usize_toNat a) (usize_toNat b) hab 0
    (zeros (a.usize + 1) (by rw [usize_succ_toNat]; exact h))
    (by rw [n_zeros, usize_succ_toNat]; omega) (by simp)

/-- `a + b`; panics if the result would exceed `maxBytes`. -/
@[expose] public def add (a b : BigNat) : BigNat :=
  if hab : b.n ≤ a.n then
    if h : (a.n + 1) * 4 ≤ maxBytes then (addCore a b hab h).normalize else panic! "out of memory"
  else
    if h : (b.n + 1) * 4 ≤ maxBytes then (addCore b a (by omega) h).normalize
    else panic! "out of memory"

/-! ## Subtraction -/

-- Differences are computed in 64 bits, taking the borrow from the sign bit.
@[expose] public def subTail (a : BigNat) (la i : USize) (hla : la.toNat = a.n) (k : UInt64) (c : BigNat)
    (hc : a.n ≤ c.n) (_hi : i.toNat ≤ la.toNat) : BigNat :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 - k
    subTail a la (i+1) hla (t >>> 63) (c.set i (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[expose] public def subLoop (a b : BigNat) (la lb i : USize) (hla : la.toNat = a.n) (hlb : lb.toNat = b.n)
    (hab : b.n ≤ a.n) (k : UInt64) (c : BigNat) (hc : a.n ≤ c.n) (hi : i.toNat ≤ lb.toNat) : BigNat :=
  if h : i < lb then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 - (b.get i (by omega)).toUInt64 - k
    subLoop a b la lb (i+1) hla hlb hab (t >>> 63) (c.set i (by omega) t.toUInt32)
      (by simp; omega) (by rw [toNat_succ_of_lt h]; omega)
  else subTail a la i hla k c hc (by have := not_lt_toNat h; omega)
termination_by lb.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `a - b` for `b.n ≤ a.n` (meaningful for `b ≤ a`), with `a.n` digits (not normalized). -/
@[expose] public def subCore (a b : BigNat) (hab : b.n ≤ a.n) : BigNat :=
  subLoop a b a.usize b.usize 0 (usize_toNat a) (usize_toNat b) hab 0
    (zeros a.usize (by rw [usize_toNat]; exact a.n_le)) (by rw [n_zeros, usize_toNat]; omega)
    (by simp)

/-- `a - b`, truncated at `0`. -/
@[expose] public def sub (a b : BigNat) : BigNat :=
  if cmp a b == .lt then empty
  else if hab : b.n ≤ a.n then (subCore a b hab).normalize else empty


public theorem toNat_add_of_lt_size {i j : USize} (h : i.toNat + j.toNat < USize.size) :
    (i + j).toNat = i.toNat + j.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow, Nat.mod_eq_of_lt h]

public theorem BigNat.n_lt_size (c : BigNat) : c.n < USize.size := by
  have := c.n_le; have := maxBytes_lt; omega

/-! ## Shifts -/

/-- `c[q + i] := a[i]` for `i < la`. -/
@[expose] public def copyLoop (a : BigNat) (la q i : USize) (hla : la.toNat = a.n) (c : BigNat)
    (hc : q.toNat + la.toNat ≤ c.n) (_hi : i.toNat ≤ la.toNat) : BigNat :=
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
@[expose] public def shlLoop (a : BigNat) (la q : USize) (s : UInt32) (i : USize) (hla : la.toNat = a.n) (prev : UInt32)
    (c : BigNat) (hc : q.toNat + la.toNat < c.n) (_hi : i.toNat ≤ la.toNat) : BigNat :=
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
@[expose] public def shiftLeft (a : BigNat) (sh : USize) : BigNat :=
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
@[expose] public def copyDown (a : BigNat) (q n : USize) (hqn : q.toNat + n.toNat ≤ a.n) (i : USize) (c : BigNat)
    (hc : n.toNat ≤ c.n) (_hi : i.toNat ≤ n.toNat) : BigNat :=
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
@[expose] public def shrLoop (a : BigNat) (q n : USize) (s : UInt32) (hqn : q.toNat + n.toNat = a.n) (i : USize) (c : BigNat)
    (hc : n.toNat ≤ c.n) (_hi : i.toNat ≤ n.toNat) : BigNat :=
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
@[expose] public def shiftRight (a : BigNat) (sh : USize) : BigNat :=
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


@[inline, expose] public def getOr0 (a : BigNat) (i : USize) : UInt32 :=
  if h : i < a.usize then a.get i (by rw [← usize_toNat]; exact USize.lt_iff_toNat_lt.mp h) else 0

/-- `c[i] := f a[i] b[i]` for `i < n`, reading digits past the end as `0`. -/
@[specialize, expose] public def zipLoop (f : UInt32 → UInt32 → UInt32) (a b : BigNat) (n i : USize) (c : BigNat)
    (hc : n.toNat ≤ c.n) (_hi : i.toNat ≤ n.toNat) : BigNat :=
  if h : i < n then
    have hi' := USize.lt_iff_toNat_lt.mp h
    zipLoop f a b n (i+1) (c.set i (by omega) (f (getOr0 a i) (getOr0 b i))) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c
termination_by n.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

@[inline, expose] public def zipWith (f : UInt32 → UInt32 → UInt32) (a b : BigNat) (n : USize)
    (hn : n.toNat ≤ max a.n b.n) : BigNat :=
  zipLoop f a b n 0 (zeros n (by have := a.n_le; have := b.n_le; omega)) (by simp) (by simp)

@[expose] public def land (a b : BigNat) : BigNat :=
  (zipWith (· &&& ·) a b (if a.usize ≤ b.usize then a.usize else b.usize) (by
    split <;> simp only [usize_toNat] <;> omega)).normalize

@[expose] public def lor (a b : BigNat) : BigNat :=
  zipWith (· ||| ·) a b (if a.usize ≤ b.usize then b.usize else a.usize) (by
    split <;> simp only [usize_toNat] <;> omega)

@[expose] public def xor (a b : BigNat) : BigNat :=
  (zipWith (· ^^^ ·) a b (if a.usize ≤ b.usize then b.usize else a.usize) (by
    split <;> simp only [usize_toNat] <;> omega)).normalize


/-! ## Single-digit operations -/

@[expose] public def mulAddSmallLoop (a : BigNat) (la : USize) (hla : la.toNat = a.n) (m : UInt64) (i : USize) (k : UInt64)
    (c : BigNat) (hc : la.toNat < c.n) (_hi : i.toNat ≤ la.toNat) : BigNat :=
  if h : i < la then
    have hi' := USize.lt_iff_toNat_lt.mp h
    let t := (a.get i (by omega)).toUInt64 * m + k
    mulAddSmallLoop a la hla m (i+1) (t >>> 32) (c.set i (by omega) t.toUInt32) (by simp; omega)
      (by rw [toNat_succ_of_lt h]; omega)
  else c.set la (by omega) k.toUInt32
termination_by la.toNat - i.toNat
decreasing_by rw [toNat_succ_of_lt h]; omega

/-- `a * m + k`. -/
@[expose] public def mulAddSmall (a : BigNat) (m k : UInt32) : BigNat :=
  if h : (a.n + 1) * 4 ≤ maxBytes then
    (mulAddSmallLoop a a.usize a.usize_toNat m.toUInt64 0 k.toUInt64
      (zeros (a.usize + 1) (by rw [a.usize_succ_toNat]; exact h))
      (by rw [n_zeros, a.usize_succ_toNat, a.usize_toNat]; omega) (by simp)).normalize
  else panic! "out of memory"

@[expose] public def div1Loop (a : BigNat) (d : UInt64) (j : USize) (hj : j.toNat ≤ a.n) (r : UInt64) (q : BigNat)
    (hq : j.toNat ≤ q.n) : BigNat × UInt64 :=
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
@[expose] public def divModSmall (a : BigNat) (d : UInt32) : BigNat × UInt32 :=
  let p := div1Loop a d.toUInt64 a.usize a.usize_le 0 (zeros a.usize (by
    rw [a.usize_toNat]; exact a.n_le)) (by rw [n_zeros]; exact Nat.le_refl _)
  (p.1.normalize, p.2.toUInt32)


public theorem two_usize_toNat : (2 : USize).toNat = 2 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h]

public theorem toNat_sub_two {i : USize} (h : 2 ≤ i.toNat) : (i - 2).toNat = i.toNat - 2 := by
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [two_usize_toNat]; omega)),
    two_usize_toNat]

public theorem eight_le_maxBytes : 8 ≤ maxBytes := by
  rcases System.Platform.numBits_eq with h | h <;> simp [maxBytes, h]

@[expose] public def ofUInt64 (x : UInt64) : BigNat :=
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

/-! ## Bit queries -/

/-- `⌊log₂ a⌋` for `a ≠ 0`, and `0` for `a = 0`. -/
@[expose] public def log2 (a : BigNat) : USize :=
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

@[expose] public def trailingZerosLoop (a : BigNat) (i : USize) (_hi : i.toNat ≤ a.n) : USize :=
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
@[expose] public def trailingZeros (a : BigNat) : USize := trailingZerosLoop a 0 (by simp)

/-- The value modulo `2^64`. -/
@[expose] public def low64 (a : BigNat) : UInt64 :=
  (getOr0 a 0).toUInt64 ||| (getOr0 a 1).toUInt64 <<< 32


/-! ## Parsing -/

public structure DecimalState where
  acc : BigNat
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
@[expose] public def ofDecimal (s : String) : BigNat :=
  let st := ofDecimalLoop s.toUTF8 0 ⟨BigNat.empty, 0, 0⟩
  mulAddSmall st.acc (pow10 st.ndig 1) st.chunk

/-! ## Printing -/

/--
The base-`10^9` digits of `a`, least significant first. Each step removes at least 29 bits, so a
budget of `2 * a.n` steps always suffices.
-/
@[expose] public def chunksLoop : Nat → BigNat → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | fuel + 1, a, acc =>
    if a.usize == 0 then acc else
      let p := divModSmall a 1000000000
      chunksLoop fuel p.1 (acc.push p.2)

/-- The decimal representation of `a`. -/
@[expose] public def toDecimal (a : BigNat) : String :=
  let chunks := chunksLoop (2 * a.n) a #[]
  if chunks.isEmpty then "0" else
    let top := toString chunks.back!
    chunks.pop.foldr (init := top) fun c s =>
      let d := toString c
      s ++ "".pushn '0' (9 - d.length) ++ d

end Nat.Big
