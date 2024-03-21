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

@[extern "lean_byte_array_uget"]
def uget : (a : @& ByteArray) → (i : USize) → i.toNat < a.size → UInt8
  | ⟨bs⟩, i, h => bs[i]

@[extern "lean_byte_array_get"]
def get! : (@& ByteArray) → (@& Nat) → UInt8
  | ⟨bs⟩, i => bs.get! i

@[extern "lean_byte_array_fget"]
def get : (a : @& ByteArray) → (@& Fin a.size) → UInt8
  | ⟨bs⟩, i => bs.get i

instance : GetElem ByteArray Nat UInt8 fun xs i => i < xs.size where
  getElem xs i h := xs.get ⟨i, h⟩

instance : GetElem ByteArray USize UInt8 fun xs i => i.val < xs.size where
  getElem xs i h := xs.uget i h

@[extern "lean_byte_array_set"]
def set! : ByteArray → (@& Nat) → UInt8 → ByteArray
  | ⟨bs⟩, i, b => ⟨bs.set! i b⟩

@[extern "lean_byte_array_fset"]
def set : (a : ByteArray) → (@& Fin a.size) → UInt8 → ByteArray
  | ⟨bs⟩, i, b => ⟨bs.set i b⟩

@[extern "lean_byte_array_uset"]
def uset : (a : ByteArray) → (i : USize) → UInt8 → i.toNat < a.size → ByteArray
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

partial def toList (bs : ByteArray) : List UInt8 :=
  let rec loop (i : Nat) (r : List UInt8) :=
    if i < bs.size then
      loop (i+1) (bs.get! i :: r)
    else
      r.reverse
  loop 0 []

@[inline] partial def findIdx? (a : ByteArray) (p : UInt8 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if i < a.size then
      if p (a.get! i) then some i else loop (i+1)
    else
      none
  loop start

/--
  We claim this unsafe implementation is correct because an array cannot have more than `usizeSz` elements in our runtime.
  This is similar to the `Array` version.

  TODO: avoid code duplication in the future after we improve the compiler.
-/
@[inline] unsafe def forInUnsafe {β : Type v} {m : Type v → Type w} [Monad m] (as : ByteArray) (b : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  let sz := USize.ofNat as.size
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
      match (← f (as.get ⟨as.size - 1 - i, this⟩) b) with
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
          loop i' (j+1) (← f b (as.get ⟨j, Nat.lt_of_lt_of_le hlt h⟩))
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
  (bs.get! 0).toUInt64 <<< 0x38 |||
  (bs.get! 1).toUInt64 <<< 0x30 |||
  (bs.get! 2).toUInt64 <<< 0x28 |||
  (bs.get! 3).toUInt64 <<< 0x20 |||
  (bs.get! 4).toUInt64 <<< 0x18 |||
  (bs.get! 5).toUInt64 <<< 0x10 |||
  (bs.get! 6).toUInt64 <<< 0x8  |||
  (bs.get! 7).toUInt64

/-- Interpret a `ByteArray` of size 8 as a big-endian `UInt64`. -/
def ByteArray.toUInt64BE! (bs : ByteArray) : UInt64 :=
  assert! bs.size == 8
  (bs.get! 7).toUInt64 <<< 0x38 |||
  (bs.get! 6).toUInt64 <<< 0x30 |||
  (bs.get! 5).toUInt64 <<< 0x28 |||
  (bs.get! 4).toUInt64 <<< 0x20 |||
  (bs.get! 3).toUInt64 <<< 0x18 |||
  (bs.get! 2).toUInt64 <<< 0x10 |||
  (bs.get! 1).toUInt64 <<< 0x8  |||
  (bs.get! 0).toUInt64
