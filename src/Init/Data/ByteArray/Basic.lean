/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.UInt.Basic
import all Init.Data.UInt.BasicAux
public import Init.Data.Array.Extract

set_option doc.verso true

@[expose] public section
universe u

namespace ByteArray

deriving instance BEq for ByteArray

attribute [ext] ByteArray

instance : DecidableEq ByteArray :=
  fun _ _ => decidable_of_decidable_of_iff ByteArray.ext_iff.symm

instance : Inhabited ByteArray where
  default := empty

instance : EmptyCollection ByteArray where
  emptyCollection := ByteArray.empty

/--
Retrieves the size of the array as a platform-specific fixed-width integer.

Because {name}`USize` is big enough to address all memory on every platform that Lean supports,
there are in practice no {name}`ByteArray`s that have more elements that {name}`USize` can count.
-/
@[extern "lean_sarray_size", simp]
def usize (a : @& ByteArray) : USize :=
  a.size.toUSize

/--
Retrieves the byte at the indicated index. Callers must prove that the index is in bounds. The index
is represented by a platform-specific fixed-width integer (either 32 or 64 bits).

Because {name}`USize` is big enough to address all memory on every platform that Lean supports, there are
in practice no {name}`ByteArray`s for which {name}`uget` cannot retrieve all elements.
-/
@[extern "lean_byte_array_uget"]
def uget : (a : @& ByteArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → UInt8
  | ⟨bs⟩, i, h => bs[i]

/--
Retrieves the byte at the indicated index. Panics if the index is out of bounds.
-/
@[extern "lean_byte_array_get"]
def get! : (@& ByteArray) → (@& Nat) → UInt8
  | ⟨bs⟩, i => bs[i]!

/--
Retrieves the byte at the indicated index. Callers must prove that the index is in bounds.

Use {name}`uget` for a more efficient alternative or {name}`get!` for a variant that panics if the
index is out of bounds.
-/
@[extern "lean_byte_array_fget"]
def get : (a : @& ByteArray) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → UInt8
  | ⟨bs⟩, i, _ => bs[i]

instance : GetElem ByteArray Nat UInt8 fun xs i => i < xs.size where
  getElem xs i h := xs.get i

instance : GetElem ByteArray USize UInt8 fun xs i => i.toFin < xs.size where
  getElem xs i h := xs.uget i h

/--
Replaces the byte at the given index.

The array is modified in-place if there are no other references to it.

If the index is out of bounds, the array is returned unmodified.
-/
@[extern "lean_byte_array_set"]
def set! : ByteArray → (@& Nat) → UInt8 → ByteArray
  | ⟨bs⟩, i, b => ⟨bs.set! i b⟩

/--
Replaces the byte at the given index.

No bounds check is performed, but the function requires a proof that the index is in bounds. This
proof can usually be omitted, and will be synthesized automatically.

The array is modified in-place if there are no other references to it.
-/
@[extern "lean_byte_array_fset"]
def set : (a : ByteArray) → (i : @& Nat) → UInt8 → (h : i < a.size := by get_elem_tactic) → ByteArray
  | ⟨bs⟩, i, b, h => ⟨bs.set i b h⟩

@[extern "lean_byte_array_uset", inherit_doc ByteArray.set]
def uset : (a : ByteArray) → (i : USize) → UInt8 → (h : i.toNat < a.size := by get_elem_tactic) → ByteArray
  | ⟨bs⟩, i, v, h => ⟨bs.uset i v h⟩

/--
Computes a hash for a {name}`ByteArray`.
-/
@[extern "lean_byte_array_hash"]
protected opaque hash (a : @& ByteArray) : UInt64

instance : Hashable ByteArray where
  hash := ByteArray.hash

/--
Returns {name}`true` when {name}`s` contains zero bytes.
-/
def isEmpty (s : ByteArray) : Bool :=
  s.size == 0

/--
Copies the slice at `[srcOff, srcOff + len)` in {name}`src` to `[destOff, destOff + len)` in
{name}`dest`, growing {name}`dest` if necessary. If {name}`exact` is {name}`false`, the capacity
will be doubled when grown.
-/
@[extern "lean_byte_array_copy_slice"]
def copySlice (src : @& ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
  ⟨dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++ dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size⟩

/--
Copies the bytes with indices {name}`b` (inclusive) to {name}`e` (exclusive) to a new
{name}`ByteArray`.
-/
def extract (a : ByteArray) (b e : Nat) : ByteArray :=
  a.copySlice b empty 0 (e - b)

/--
Appends two byte arrays using fast array primitives instead of converting them into lists and back.

In compiled code, this function replaces calls to {name}`ByteArray.append`.
-/
@[inline]
protected def fastAppend (a : ByteArray) (b : ByteArray) : ByteArray :=
  -- we assume that `append`s may be repeated, so use asymptotic growing; use `copySlice` directly to customize
  b.copySlice 0 a a.size b.size false

@[simp]
theorem size_data {a : ByteArray} :
  a.data.size = a.size := rfl

@[csimp]
theorem append_eq_fastAppend : @ByteArray.append = @ByteArray.fastAppend := by
  funext a b
  ext1
  apply Array.ext'
  simp [ByteArray.fastAppend, copySlice, ← size_data, - Array.append_assoc]

-- Needs to come after the `csimp` lemma
instance : Append ByteArray where
  append := ByteArray.append

@[simp]
theorem append_eq {a b : ByteArray} : a.append b = a ++ b := rfl

@[simp]
theorem fastAppend_eq {a b : ByteArray} : a.fastAppend b = a ++ b := by
  simp [← append_eq_fastAppend]

/--
Converts a packed array of bytes to a linked list.
-/
def toList (bs : ByteArray) : List UInt8 :=
  let rec loop (i : Nat) (r : List UInt8) :=
    if i < bs.size then
      loop (i+1) (bs.get! i :: r)
    else
      r.reverse
    termination_by bs.size - i
    decreasing_by decreasing_trivial_pre_omega
  loop 0 []

/--
Finds the index of the first byte in {name}`a` for which {name}`p` returns {name}`true`. If no byte
in {name}`a` satisfies {name}`p`, then the result is {name}`none`.

The index is returned along with a proof that it is a valid index in the array.
-/
@[inline] def findFinIdx? (a : ByteArray) (p : UInt8 → Bool) (start := 0) : Option (Fin a.size) :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some ⟨i, h⟩ else loop (i+1)
    else
      none
    termination_by a.size - i
    decreasing_by decreasing_trivial_pre_omega
  loop start

/--
Finds the index of the first byte in {name}`a` for which {name}`p` returns {name}`true`. If no byte
in {name}`a` satisfies {name}`p`, then the result is {name}`none`.

The variant {name}`findFinIdx?` additionally returns a proof that the found index is in bounds.
-/
@[inline] def findIdx? (a : ByteArray) (p : UInt8 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if h : i < a.size then
      if p a[i] then some i else loop (i+1)
    else
      none
    termination_by a.size - i
    decreasing_by decreasing_trivial_pre_omega
  loop start

/--
An efficient implementation of {name}`ForIn.forIn` for {name}`ByteArray` that uses {name}`USize`
rather than {name}`Nat` for indices.

We claim this unsafe implementation is correct because an array cannot have more than
{name}`USize.size` elements in our runtime. This is similar to the {name}`Array` version.
-/
-- TODO: avoid code duplication in the future after we improve the compiler.
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

/--
The reference implementation of {name}`ForIn.forIn` for {name}`ByteArray`.

In compiled code, this is replaced by the more efficient {name}`ByteArray.forInUnsafe`.
-/
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

instance [Monad m] : ForIn m ByteArray UInt8 where
  forIn := ByteArray.forIn

/--
An efficient implementation of a monadic left fold on for {name}`ByteArray` that uses {name}`USize`
rather than {name}`Nat` for indices.

We claim this unsafe implementation is correct because an array cannot have more than
{name}`USize.size` elements in our runtime. This is similar to the {name}`Array` version.
-/
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
    else if start < as.size then
      fold (USize.ofNat start) (USize.ofNat as.size) init
    else
      pure init
  else
    pure init

/--
A monadic left fold on {name}`ByteArray` that iterates over an array from low to high indices,
computing a running value.

Each element of the array is combined with the value from the prior elements using a monadic
function {name}`f`. The initial value {name}`init` is the starting value before any elements have
been processed.
-/
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

/--
A left fold on {name}`ByteArray` that iterates over an array from low to high indices, computing a
running value.

Each element of the array is combined with the value from the prior elements using a function
{name}`f`. The initial value {name}`init` is the starting value before any elements have been
processed.

{name}`ByteArray.foldlM` is a monadic variant of this function.
-/
@[inline]
def foldl {β : Type v} (f : β → UInt8 → β) (init : β) (as : ByteArray) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM (pure <| f · ·) init start stop

set_option doc.verso false -- Awaiting intra-module forward reference support
/--
Iterator over the bytes (`UInt8`) of a `ByteArray`.

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
set_option doc.verso true

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

/--
The number of bytes remaining in the iterator.
-/
def remainingBytes : Iterator → Nat
  | ⟨arr, i⟩ => arr.size - i

@[inherit_doc Iterator.idx]
def pos := Iterator.idx

/-- True if the iterator is past the array's last byte. -/
@[inline]
def atEnd : Iterator → Bool
  | ⟨arr, i⟩ => i ≥ arr.size

/--
The byte at the current position.

On an invalid position, returns {lean}`(default : UInt8)`.
-/
@[inline]
def curr : Iterator → UInt8
  | ⟨arr, i⟩ =>
    if h : i < arr.size then
      arr[i]'h
    else
      default

/--
Moves the iterator's position forward by one byte, unconditionally.

It is only valid to call this function if the iterator is not at the end of the array, *i.e.*
{name}`Iterator.atEnd` is {name}`false`; otherwise, the resulting iterator will be invalid.
-/
@[inline]
def next : Iterator → Iterator
  | ⟨arr, i⟩ => ⟨arr, i + 1⟩

/--
Decreases the iterator's position.

If the position is zero, this function is the identity.
-/
@[inline]
def prev : Iterator → Iterator
  | ⟨arr, i⟩ => ⟨arr, i - 1⟩

/--
True if the iterator is valid; that is, it is not past the array's last byte.
-/
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

/--
Moves the iterator's position to the end of the array.

Given {given}`i : ByteArray.Iterator`, note that {lean}`i.toEnd.atEnd` is always {name}`true`.
-/
@[inline]
def toEnd : Iterator → Iterator
  | ⟨arr, _⟩ => ⟨arr, arr.size⟩

/--
Moves the iterator's position several bytes forward.

The resulting iterator is only valid if the number of bytes to skip is less than or equal to
the number of bytes left in the iterator.
-/
@[inline]
def forward : Iterator → Nat → Iterator
  | ⟨arr, i⟩, f => ⟨arr, i + f⟩

@[inherit_doc forward, inline]
def nextn : Iterator → Nat → Iterator := forward

/--
Moves the iterator's position several bytes back.

If asked to go back more bytes than available, stops at the beginning of the array.
-/
@[inline]
def prevn : Iterator → Nat → Iterator
  | ⟨arr, i⟩, f => ⟨arr, i - f⟩

end Iterator
end ByteArray

instance : ToString ByteArray := ⟨fun bs => bs.toList.toString⟩
