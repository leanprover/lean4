/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Array.Subarray
import Init.Data.UInt.Basic
import Init.Data.Option.Basic
universe u

structure ByteArray where
  data : Array UInt8

attribute [extern "lean_byte_array_mk"] ByteArray.mk
attribute [extern "lean_byte_array_data"] ByteArray.data

namespace ByteArray
@[extern "lean_mk_empty_byte_array"]
def mkEmpty (c : @& Nat) : ByteArray :=
  { data := #[] }

def empty : ByteArray := mkEmpty 0

instance : Inhabited ByteArray where
  default := empty

instance : EmptyCollection ByteArray where
  emptyCollection := ByteArray.empty

@[extern "lean_byte_array_push"]
def push : ByteArray → UInt8 → ByteArray
  | ⟨bs⟩, b => ⟨bs.push b⟩

@[extern "lean_byte_array_size"]
def size : (@& ByteArray) → Nat
  | ⟨bs⟩ => bs.size

@[extern "lean_sarray_size", simp]
def usize (a : @& ByteArray) : USize :=
  a.size.toUSize

@[extern "lean_byte_array_uget"]
def uget : (a : @& ByteArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → UInt8
  | ⟨bs⟩, i, h => bs[i]

@[extern "lean_byte_array_get"]
def get! : (@& ByteArray) → (@& Nat) → UInt8
  | ⟨bs⟩, i => bs.get! i

@[extern "lean_byte_array_fget"]
def get : (a : @& ByteArray) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → UInt8
  | ⟨bs⟩, i, _ => bs[i]

instance : GetElem ByteArray Nat UInt8 fun xs i => i < xs.size where
  getElem xs i h := xs.get i

instance : GetElem ByteArray USize UInt8 fun xs i => i.val < xs.size where
  getElem xs i h := xs.uget i h

@[extern "lean_byte_array_set"]
def set! : ByteArray → (@& Nat) → UInt8 → ByteArray
  | ⟨bs⟩, i, b => ⟨bs.set! i b⟩

@[extern "lean_byte_array_fset"]
def set : (a : ByteArray) → (i : @& Nat) → UInt8 → (h : i < a.size := by get_elem_tactic) → ByteArray
  | ⟨bs⟩, i, b, h => ⟨bs.set i b h⟩

@[extern "lean_byte_array_uset"]
def uset : (a : ByteArray) → (i : USize) → UInt8 → (h : i.toNat < a.size := by get_elem_tactic) → ByteArray
  | ⟨bs⟩, i, v, h => ⟨bs.uset i v h⟩

@[extern "lean_byte_array_hash"]
protected opaque hash (a : @& ByteArray) : UInt64

instance : Hashable ByteArray where
  hash := ByteArray.hash

def isEmpty (s : ByteArray) : Bool :=
  s.size == 0

/--
  Copy the slice at `[srcOff, srcOff + len)` in `src` to `[destOff, destOff + len)` in `dest`, growing `dest` if necessary.
  If `exact` is `false`, the capacity will be doubled when grown. -/
@[extern "lean_byte_array_copy_slice"]
def copySlice (src : @& ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
  ⟨dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++ dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size⟩

def extract (a : ByteArray) (b e : Nat) : ByteArray :=
  a.copySlice b empty 0 (e - b)

protected def append (a : ByteArray) (b : ByteArray) : ByteArray :=
  -- we assume that `append`s may be repeated, so use asymptotic growing; use `copySlice` directly to customize
  b.copySlice 0 a a.size b.size false

instance : Append ByteArray := ⟨ByteArray.append⟩

def toList (bs : ByteArray) : List UInt8 :=
  let rec loop (i : Nat) (r : List UInt8) :=
    if i < bs.size then
      loop (i+1) (bs.get! i :: r)
    else
      r.reverse
    termination_by bs.size - i
    decreasing_by decreasing_trivial_pre_omega
  loop 0 []

@[inline] def findIdx? (a : ByteArray) (p : UInt8 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if i < a.size then
      if p (a.get! i) then some i else loop (i+1)
    else
      none
    termination_by a.size - i
    decreasing_by decreasing_trivial_pre_omega
  loop start

/--
  We claim this unsafe implementation is correct because an array cannot have more than `usizeSz` elements in our runtime.
  This is similar to the `Array` version.

  TODO: avoid code duplication in the future after we improve the compiler.
-/
@[inline] unsafe def forInUnsafe {β : Type v} {m : Type v → Type w} [Monad m] (as : ByteArray) (b : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

/-- Reference implementation for `forIn` -/
@[implemented_by ByteArray.forInUnsafe]
protected def forIn {β : Type v} {m : Type v → Type w} [Monad m] (as : ByteArray) (b : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance : ForIn m ByteArray UInt8 where
  forIn := ByteArray.forIn

/-- See comment at `forInUnsafe` -/
-- TODO: avoid code duplication.
@[inline]
unsafe def foldlMUnsafe {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt8 → m β) (init : β) (as : ByteArray) (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else
    pure init

/-- Reference implementation for `foldlM` -/
@[implemented_by foldlMUnsafe]
def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → UInt8 → m β) (init : β) (as : ByteArray) (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          loop i' (j+1) (← f b as[j])
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

@[inline]
def foldl {β : Type v} (f : β → UInt8 → β) (init : β) (as : ByteArray) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM f init start stop

/-- Iterator over the bytes (`UInt8`) of a `ByteArray`.

Typically created by `arr.iter`, where `arr` is a `ByteArray`.

An iterator is *valid* if the position `i` is *valid* for the array `arr`, meaning `0 ≤ i ≤ arr.size`

Most operations on iterators return arbitrary values if the iterator is not valid. The functions in
the `ByteArray.Iterator` API should rule out the creation of invalid iterators, with two exceptions:

- `Iterator.next iter` is invalid if `iter` is already at the end of the array (`iter.atEnd` is
  `true`)
- `Iterator.forward iter n`/`Iterator.nextn iter n` is invalid if `n` is strictly greater than the
  number of remaining bytes.
-/
structure Iterator where
  /-- The array the iterator is for. -/
  array : ByteArray
  /-- The current position.

  This position is not necessarily valid for the array, for instance if one keeps calling
  `Iterator.next` when `Iterator.atEnd` is true. If the position is not valid, then the
  current byte is `(default : UInt8)`. -/
  idx : Nat
  deriving Inhabited

/-- Creates an iterator at the beginning of an array. -/
def mkIterator (arr : ByteArray) : Iterator :=
  ⟨arr, 0⟩

@[inherit_doc mkIterator]
abbrev iter := mkIterator

/-- The size of an array iterator is the number of bytes remaining. -/
instance : SizeOf Iterator where
  sizeOf i := i.array.size - i.idx

theorem Iterator.sizeOf_eq (i : Iterator) : sizeOf i = i.array.size - i.idx :=
  rfl

namespace Iterator

/-- Number of bytes remaining in the iterator. -/
def remainingBytes : Iterator → Nat
  | ⟨arr, i⟩ => arr.size - i

@[inherit_doc Iterator.idx]
def pos := Iterator.idx

/-- The byte at the current position.

On an invalid position, returns `(default : UInt8)`. -/
@[inline]
def curr : Iterator → UInt8
  | ⟨arr, i⟩ =>
    if h : i < arr.size then
      arr[i]'h
    else
      default

/-- Moves the iterator's position forward by one byte, unconditionally.

It is only valid to call this function if the iterator is not at the end of the array, *i.e.*
`Iterator.atEnd` is `false`; otherwise, the resulting iterator will be invalid. -/
@[inline]
def next : Iterator → Iterator
  | ⟨arr, i⟩ => ⟨arr, i + 1⟩

/-- Decreases the iterator's position.

If the position is zero, this function is the identity. -/
@[inline]
def prev : Iterator → Iterator
  | ⟨arr, i⟩ => ⟨arr, i - 1⟩

/-- True if the iterator is past the array's last byte. -/
@[inline]
def atEnd : Iterator → Bool
  | ⟨arr, i⟩ => i ≥ arr.size

/-- True if the iterator is not past the array's last byte. -/
@[inline]
def hasNext : Iterator → Bool
  | ⟨arr, i⟩ => i < arr.size

/-- The byte at the current position. --/
@[inline]
def curr' (it : Iterator) (h : it.hasNext) : UInt8 :=
  match it with
  | ⟨arr, i⟩ =>
    have : i < arr.size := by
      simp only [hasNext, decide_eq_true_eq] at h
      assumption
    arr[i]

/-- Moves the iterator's position forward by one byte. --/
@[inline]
def next' (it : Iterator) (_h : it.hasNext) : Iterator :=
  match it with
  | ⟨arr, i⟩ => ⟨arr, i + 1⟩

/-- True if the position is not zero. -/
@[inline]
def hasPrev : Iterator → Bool
  | ⟨_, i⟩ => i > 0

/-- Moves the iterator's position to the end of the array.

Note that `i.toEnd.atEnd` is always `true`. -/
@[inline]
def toEnd : Iterator → Iterator
  | ⟨arr, _⟩ => ⟨arr, arr.size⟩

/-- Moves the iterator's position several bytes forward.

The resulting iterator is only valid if the number of bytes to skip is less than or equal to
the number of bytes left in the iterator. -/
@[inline]
def forward : Iterator → Nat → Iterator
  | ⟨arr, i⟩, f => ⟨arr, i + f⟩

@[inherit_doc forward, inline]
def nextn : Iterator → Nat → Iterator := forward

/-- Moves the iterator's position several bytes back.

If asked to go back more bytes than available, stops at the beginning of the array. -/
@[inline]
def prevn : Iterator → Nat → Iterator
  | ⟨arr, i⟩, f => ⟨arr, i - f⟩

end Iterator
end ByteArray

def List.toByteArray (bs : List UInt8) : ByteArray :=
  let rec loop
    | [],    r => r
    | b::bs, r => loop bs (r.push b)
  loop bs ByteArray.empty

instance : ToString ByteArray := ⟨fun bs => bs.toList.toString⟩

/-- Interpret a `ByteArray` of size 8 as a little-endian `UInt64`. -/
def ByteArray.toUInt64LE! (bs : ByteArray) : UInt64 :=
  assert! bs.size == 8
  (bs.get! 7).toUInt64 <<< 0x38 |||
  (bs.get! 6).toUInt64 <<< 0x30 |||
  (bs.get! 5).toUInt64 <<< 0x28 |||
  (bs.get! 4).toUInt64 <<< 0x20 |||
  (bs.get! 3).toUInt64 <<< 0x18 |||
  (bs.get! 2).toUInt64 <<< 0x10 |||
  (bs.get! 1).toUInt64 <<< 0x8  |||
  (bs.get! 0).toUInt64

/-- Interpret a `ByteArray` of size 8 as a big-endian `UInt64`. -/
def ByteArray.toUInt64BE! (bs : ByteArray) : UInt64 :=
  assert! bs.size == 8
  (bs.get! 0).toUInt64 <<< 0x38 |||
  (bs.get! 1).toUInt64 <<< 0x30 |||
  (bs.get! 2).toUInt64 <<< 0x28 |||
  (bs.get! 3).toUInt64 <<< 0x20 |||
  (bs.get! 4).toUInt64 <<< 0x18 |||
  (bs.get! 5).toUInt64 <<< 0x10 |||
  (bs.get! 6).toUInt64 <<< 0x8  |||
  (bs.get! 7).toUInt64
