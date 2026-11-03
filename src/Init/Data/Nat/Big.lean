/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.Data.ByteArray.Extra
public import Init.Data.String.Defs
public import Init.Data.Ord.Basic
public import Init.Data.UInt.Log2
public import Init.Data.UInt.Basic
public import Init.Data.Repr
public import Init.Data.Array.Basic

/-!
# Big number magnitudes

The runtime represents a natural number that does not fit into a scalar as a `ByteArray` of
little-endian 32-bit digits without leading zero digits (a *magnitude*). This module implements
arithmetic on magnitudes; `Init.Data.Nat.BigRuntime` builds the runtime's big `Nat` and `Int`
primitives on top of it.

The functions are `unsafe` because they access digits without bounds checks. They must not create
big `Nat`s themselves, as that would call back into them, so all counting uses `USize`.
-/

namespace Nat.Big

/-- The number of digits. -/
@[inline] public def size (a : @& ByteArray) : USize := a.usize >>> 2

@[inline] public unsafe def get (a : @& ByteArray) (i : USize) : UInt32 :=
  a.ugetUInt32LE (i <<< 2) lcProof

@[inline] public unsafe def set (a : ByteArray) (i : USize) (v : UInt32) : ByteArray :=
  a.usetUInt32LE (i <<< 2) v lcProof

@[inline] unsafe def getOr0 (a : @& ByteArray) (n i : USize) : UInt32 :=
  if i < n then get a i else 0

/-- `n` zero digits. -/
@[inline] public def zeros (n : USize) : ByteArray := ByteArray.replicate (n <<< 2).toNat 0

/-- Copies digits `[srcOff, srcOff + n)` of `src` to `dst[dstOff, dstOff + n)`. -/
@[inline] def copyDigits (src : @& ByteArray) (srcOff : USize) (dst : ByteArray) (dstOff n : USize) :
    ByteArray :=
  src.copySlice (srcOff <<< 2).toNat dst (dstOff <<< 2).toNat (n <<< 2).toNat

unsafe def topNonzero (a : @& ByteArray) (n : USize) : USize :=
  if n > 0 && get a (n-1) == 0 then topNonzero a (n-1) else n

/-- Drops leading zero digits. -/
@[inline] public unsafe def normalize (a : ByteArray) : ByteArray :=
  let n := size a
  let m := topNonzero a n
  if m == n then a else a.shrink (m <<< 2).toNat

public unsafe def ofUInt64 (x : UInt64) : ByteArray :=
  normalize (set (set (zeros 2) 0 x.toUInt32) 1 (x >>> 32).toUInt32)

/-- The value modulo `2^64`. -/
public unsafe def low64 (a : @& ByteArray) : UInt64 :=
  let n := size a
  (getOr0 a n 0).toUInt64 ||| (getOr0 a n 1).toUInt64 <<< 32

/-! ## Comparison -/

unsafe def cmpLoop (a b : @& ByteArray) (i : USize) : Ordering :=
  if i == 0 then .eq else
    let x := get a (i-1)
    let y := get b (i-1)
    if x != y then (if x < y then .lt else .gt) else cmpLoop a b (i-1)

public unsafe def cmp (a b : @& ByteArray) : Ordering :=
  let la := size a
  let lb := size b
  if la != lb then (if la < lb then .lt else .gt) else cmpLoop a b la

/-! ## Addition and subtraction -/

unsafe def addTail (a : @& ByteArray) (la i : USize) (k : UInt64) (c : ByteArray) : ByteArray :=
  if i < la then
    let t := (get a i).toUInt64 + k
    addTail a la (i+1) (t >>> 32) (set c i t.toUInt32)
  else set c i k.toUInt32

unsafe def addLoop (a b : @& ByteArray) (la lb i : USize) (k : UInt64) (c : ByteArray) : ByteArray :=
  if i < lb then
    let t := (get a i).toUInt64 + (get b i).toUInt64 + k
    addLoop a b la lb (i+1) (t >>> 32) (set c i t.toUInt32)
  else addTail a la i k c

public unsafe def add (a b : @& ByteArray) : ByteArray :=
  let la := size a
  let lb := size b
  if la < lb then add b a else
    normalize (addLoop a b la lb 0 0 (zeros (la + 1)))

-- Differences are computed in 64 bits, taking the borrow from the sign bit.
unsafe def subTail (a : @& ByteArray) (la i : USize) (k : UInt64) (c : ByteArray) : ByteArray :=
  if i < la then
    let t := (get a i).toUInt64 - k
    subTail a la (i+1) (t >>> 63) (set c i t.toUInt32)
  else c

unsafe def subLoop (a b : @& ByteArray) (la lb i : USize) (k : UInt64) (c : ByteArray) : ByteArray :=
  if i < lb then
    let t := (get a i).toUInt64 - (get b i).toUInt64 - k
    subLoop a b la lb (i+1) (t >>> 63) (set c i t.toUInt32)
  else subTail a la i k c

/-- `a - b` for `a ≥ b`. -/
public unsafe def sub (a b : @& ByteArray) : ByteArray :=
  normalize (subLoop a b (size a) (size b) 0 0 (zeros (size a)))

/-! ## Multiplication -/

unsafe def mulInner (a : @& ByteArray) (la j : USize) (v : UInt64) (i : USize) (k : UInt64)
    (c : ByteArray) : ByteArray :=
  if i < la then
    let t := (get a i).toUInt64 * v + (get c (i+j)).toUInt64 + k
    mulInner a la j v (i+1) (t >>> 32) (set c (i+j) t.toUInt32)
  else set c (j+la) k.toUInt32

unsafe def mulOuter (a b : @& ByteArray) (la lb j : USize) (c : ByteArray) : ByteArray :=
  if j < lb then
    let v := get b j
    mulOuter a b la lb (j+1) (if v == 0 then c else mulInner a la j v.toUInt64 0 0 c)
  else c

public unsafe def mul (a b : @& ByteArray) : ByteArray :=
  let la := size a
  let lb := size b
  if la < lb then mul b a
  else if lb == 0 then zeros 0
  else normalize (mulOuter a b la lb 0 (zeros (la + lb)))

unsafe def mulAddSmallLoop (a : @& ByteArray) (la : USize) (m : UInt64) (i : USize) (k : UInt64)
    (c : ByteArray) : ByteArray :=
  if i < la then
    let t := (get a i).toUInt64 * m + k
    mulAddSmallLoop a la m (i+1) (t >>> 32) (set c i t.toUInt32)
  else set c la k.toUInt32

/-- `a * m + k`. -/
public unsafe def mulAddSmall (a : @& ByteArray) (m k : UInt32) : ByteArray :=
  normalize (mulAddSmallLoop a (size a) m.toUInt64 0 k.toUInt64 (zeros (size a + 1)))

/-! ## Shifts -/

/--
`dst[off + i] := src[i] << s | src[i-1] >> (32 - s)` for `i ≤ n` (with `src[-1] = src[n] = 0`),
for `0 < s < 32`.
-/
unsafe def shlDigits (src : @& ByteArray) (s : UInt32) (n off i : USize) (prev : UInt32)
    (dst : ByteArray) : ByteArray :=
  if i < n then
    let x := get src i
    shlDigits src s n off (i+1) x (set dst (off+i) ((x <<< s) ||| (prev >>> (32 - s))))
  else set dst (off+n) (prev >>> (32 - s))

/--
`dst[i] := src[off + i] >> s | src[off + i + 1] << (32 - s)` for `i < n` (with digits of `src`
past `la` being 0), for `0 < s < 32`.
-/
unsafe def shrDigits (src : @& ByteArray) (s : UInt32) (la off n i : USize) (dst : ByteArray) :
    ByteArray :=
  if i < n then
    let x := (get src (off+i) >>> s) ||| (getOr0 src la (off+i+1) <<< (32 - s))
    shrDigits src s la off n (i+1) (set dst i x)
  else dst

public unsafe def shiftLeft (a : @& ByteArray) (sh : USize) : ByteArray :=
  let la := size a
  if la == 0 then a else
    let q := sh >>> 5
    let s := (sh &&& 31).toUInt32
    let c := zeros (la + q + 1)
    normalize <| if s == 0 then copyDigits a 0 c q la else shlDigits a s la q 0 0 c

public unsafe def shiftRight (a : @& ByteArray) (sh : USize) : ByteArray :=
  let la := size a
  let q := sh >>> 5
  if q ≥ la then zeros 0 else
    let s := (sh &&& 31).toUInt32
    let n := la - q
    normalize <| if s == 0 then copyDigits a q (zeros n) 0 n else shrDigits a s la q n 0 (zeros n)

/-! ## Division -/

unsafe def div1Loop (a : @& ByteArray) (d : UInt64) (j : USize) (r : UInt64) (q : ByteArray) :
    ByteArray × UInt64 :=
  if j > 0 then
    let t := (r <<< 32) ||| (get a (j-1)).toUInt64
    -- `%` (not `t - (t / d) * d`) lets the C compiler reuse the remainder of the same division
    div1Loop a d (j-1) (t % d) (set q (j-1) (t / d).toUInt32)
  else (q, r)

/-- Quotient and remainder by a nonzero single digit `d`. -/
public unsafe def divModSmall (a : @& ByteArray) (d : UInt32) : ByteArray × UInt32 :=
  let (q, r) := div1Loop a d.toUInt64 (size a) 0 (zeros (size a))
  (normalize q, r.toUInt32)

@[inline] def BASE : UInt64 := 0x100000000

/-- Knuth's correction of the estimated quotient digit `qh`. -/
unsafe def recheck (qh rh vtop vsec unext : UInt64) : UInt64 :=
  if qh ≥ BASE || qh * vsec > (rh <<< 32) + unext then
    let qh := qh - 1
    let rh := rh + vtop
    if rh < BASE then recheck qh rh vtop vsec unext else qh
  else qh

/-- `ms[0..n] := q * v[0..n)`. -/
unsafe def mul1Loop (q : UInt64) (v : @& ByteArray) (n i : USize) (k : UInt64) (ms : ByteArray) :
    ByteArray :=
  if i < n then
    let t := q * (get v i).toUInt64 + k
    mul1Loop q v n (i+1) (t >>> 32) (set ms i t.toUInt32)
  else set ms n k.toUInt32

/-- `u[off..off+len) -= b[0..len)`, dropping the final borrow. -/
unsafe def subInPlace (b : @& ByteArray) (len off i : USize) (k : UInt64) (u : ByteArray) :
    ByteArray :=
  if i < len then
    let t := (get u (off+i)).toUInt64 - (get b i).toUInt64 - k
    subInPlace b len off (i+1) (t >>> 63) (set u (off+i) t.toUInt32)
  else u

/-- `u[off..off+len) += v[0..n)` (with `v[i] = 0` for `i ≥ n`), dropping the final carry. -/
unsafe def addInPlace (v : @& ByteArray) (n len off i : USize) (k : UInt64) (u : ByteArray) :
    ByteArray :=
  if i < len then
    let t := (getOr0 v n i).toUInt64 + (get u (off+i)).toUInt64 + k
    addInPlace v n len off (i+1) (t >>> 32) (set u (off+i) t.toUInt32)
  else u

/-- Knuth's algorithm D on the normalized `u` (`m + n` digits) and `v` (`n ≥ 2` digits). -/
unsafe def divNLoop (v : @& ByteArray) (n : USize) (vtop vsec : UInt64) (j1 : USize)
    (q u ms : ByteArray) : ByteArray × ByteArray :=
  if j1 == 0 then (q, u) else
    let j := j1 - 1
    let temp := ((get u (j+n)).toUInt64 <<< 32) ||| (get u (j+n-1)).toUInt64
    let qh := recheck (temp / vtop) (temp % vtop) vtop vsec (get u (j+n-2)).toUInt64
    let ms := mul1Loop qh v n 0 0 ms
    let u := subInPlace ms (n+1) j 0 0 u
    -- The `n+1`-digit difference lies in `[-v, v)`, so it borrowed iff its top digit is nonzero.
    if get u (j+n) != 0 then
      divNLoop v n vtop vsec j (set q j (qh.toUInt32 - 1)) (addInPlace v n (n+1) j 0 0 u) ms
    else
      divNLoop v n vtop vsec j (set q j qh.toUInt32) u ms

/-- Quotient and remainder by a nonzero `b`. -/
public unsafe def divMod (a b : @& ByteArray) : ByteArray × ByteArray :=
  let la := size a
  let lb := size b
  if cmp a b == .lt then (zeros 0, a)
  else if lb == 1 then
    let (q, r) := divModSmall a (get b 0)
    (q, ofUInt64 r.toUInt64)
  else
    -- normalize so that the top digit of the divisor has its high bit set
    let s := 31 - (get b (lb-1)).log2
    let v := if s == 0 then b else shlDigits b s lb 0 0 0 (zeros (lb + 1))
    let u := if s == 0 then copyDigits a 0 (zeros (la + 1)) 0 la else shlDigits a s la 0 0 0 (zeros (la + 1))
    let (q, u) := divNLoop v lb (get v (lb-1)).toUInt64 (get v (lb-2)).toUInt64 (la - lb + 1)
      (zeros (la - lb + 1)) u (zeros (lb + 1))
    let r := if s == 0 then copyDigits u 0 (zeros lb) 0 lb else shrDigits u s (lb + 1) 0 lb 0 (zeros lb)
    (normalize q, normalize r)

/-! ## Bitwise operations -/

@[specialize] unsafe def zipLoop (f : UInt32 → UInt32 → UInt32) (a b : @& ByteArray) (la lb n i : USize)
    (c : ByteArray) : ByteArray :=
  if i < n then zipLoop f a b la lb n (i+1) (set c i (f (getOr0 a la i) (getOr0 b lb i))) else c

public unsafe def land (a b : @& ByteArray) : ByteArray :=
  let la := size a
  let lb := size b
  let n := min la lb
  normalize (zipLoop (· &&& ·) a b la lb n 0 (zeros n))

public unsafe def lor (a b : @& ByteArray) : ByteArray :=
  let la := size a
  let lb := size b
  let n := max la lb
  zipLoop (· ||| ·) a b la lb n 0 (zeros n)

public unsafe def xor (a b : @& ByteArray) : ByteArray :=
  let la := size a
  let lb := size b
  let n := max la lb
  normalize (zipLoop (· ^^^ ·) a b la lb n 0 (zeros n))

/-- `⌊log₂ a⌋` for `a ≠ 0`. -/
public unsafe def log2 (a : @& ByteArray) : USize :=
  let n := size a
  ((n - 1) <<< 5) + (get a (n-1)).log2.toUSize

unsafe def ctz32 (x : UInt32) (i : USize) : USize :=
  if x &&& 1 == 0 then ctz32 (x >>> 1) (i+1) else i

unsafe def trailingZerosLoop (a : @& ByteArray) (i : USize) : USize :=
  let x := get a i
  if x == 0 then trailingZerosLoop a (i+1) else (i <<< 5) + ctz32 x 0

/-- The number of trailing zero bits of `a ≠ 0`. -/
public unsafe def trailingZeros (a : @& ByteArray) : USize := trailingZerosLoop a 0

/-! ## Powers and gcd -/

-- A function rather than a constant: magnitudes are needed before this module is initialized.
@[inline] public unsafe def one (_ : Unit) : ByteArray := ofUInt64 1

unsafe def powLoop (base : ByteArray) (e : USize) (acc : ByteArray) : ByteArray :=
  if e == 0 then acc else
    let acc := if e &&& 1 == 1 then mul acc base else acc
    if e == 1 then acc else powLoop (mul base base) (e >>> 1) acc

public unsafe def pow (a : @& ByteArray) (e : USize) : ByteArray := powLoop a e (one ())

public unsafe def gcd (a b : ByteArray) : ByteArray :=
  if size b == 0 then a else gcd b (divMod a b).2

unsafe def powModLoop (e m : @& ByteArray) (nbits i : USize) (base acc : ByteArray) : ByteArray :=
  if i < nbits then
    let bit := (get e (i >>> 5) >>> (i &&& 31).toUInt32) &&& 1
    let acc := if bit == 1 then (divMod (mul acc base) m).2 else acc
    let base := if i + 1 < nbits then (divMod (mul base base) m).2 else base
    powModLoop e m nbits (i+1) base acc
  else acc

/-- `a ^ e % m` for `m > 1`. -/
public unsafe def powMod (a e m : @& ByteArray) : ByteArray :=
  if size e == 0 then one () else powModLoop e m (log2 e + 1) 0 (divMod a m).2 (one ())

/-! ## Decimal conversion -/

structure DecimalState where
  acc : ByteArray
  chunk : UInt32
  ndig : UInt32

unsafe def ofDecimalStep (st : DecimalState) (c : UInt8) : DecimalState :=
  if '0'.toUInt8 ≤ c && c ≤ '9'.toUInt8 then
    let chunk := st.chunk * 10 + (c - '0'.toUInt8).toUInt32
    if st.ndig + 1 == 9 then ⟨mulAddSmall st.acc 1000000000 chunk, 0, 0⟩
    else ⟨st.acc, chunk, st.ndig + 1⟩
  else st

unsafe def pow10 (n acc : UInt32) : UInt32 := if n == 0 then acc else pow10 (n - 1) (acc * 10)

/-- Parses the decimal digits of `s`, ignoring all other characters. -/
public unsafe def ofDecimal (s : @& String) : ByteArray :=
  let st := s.toUTF8.foldl ofDecimalStep ⟨zeros 0, 0, 0⟩
  mulAddSmall st.acc (pow10 st.ndig 1) st.chunk

unsafe def chunksLoop (a : ByteArray) (acc : Array UInt32) : Array UInt32 :=
  if size a == 0 then acc else
    let (q, r) := divModSmall a 1000000000
    chunksLoop q (acc.push r)

/-- The decimal representation of `a`. -/
public unsafe def toDecimal (a : @& ByteArray) : String :=
  let chunks := chunksLoop a #[]
  if chunks.isEmpty then "0" else
    let top := toString chunks.back!
    chunks.pop.foldr (init := top) fun c s =>
      let d := toString c
      s ++ "".pushn '0' (9 - d.utf8ByteSize) ++ d

end Nat.Big
