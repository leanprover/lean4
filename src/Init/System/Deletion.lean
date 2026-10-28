/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

prelude
public import Init.Internal.Order.MonadTail
public import Init.Data.SInt.Basic
import Init.Data.UInt.Lemmas

/-!
# Reference-counting deletion

The deletion cascade deletes an object whose last reference has just been released, and every
object that thereby loses its last reference. It is written once over the object operations of
`Ops`, so that the same definitions run over any heap. Objects whose last reference goes are queued
on a last-in, first-out worklist linked through their headers. Each object releases the references
its slots hold before it is reclaimed.

`lean_dec_ref_cold` in `src/runtime/object.cpp` decides whether a reference was the last, and then
runs the cascade on the runtime's heap through `Native.cascade`. `tests/misc_dir/rc_deletion` proves
that on the ownership graph of its specification the cascade computes `drain`, and touches no object
outside the access protocol of its heap.
-/

public section

namespace Lean.Runtime.Deletion

/-- `#define LeanMaxCtorTag 243`, the largest constructor tag. The kinds below are `lean.h`'s. -/
abbrev LeanMaxCtorTag : UInt8 := 243
/-- `#define LeanPromise 244` -/
abbrev LeanPromise : UInt8 := 244
/-- `#define LeanClosure 245` -/
abbrev LeanClosure : UInt8 := 245
/-- `#define LeanArray 246` -/
abbrev LeanArray : UInt8 := 246
/-- `#define LeanStructArray 247`, which no runtime object has. -/
abbrev LeanStructArray : UInt8 := 247
/-- `#define LeanScalarArray 248` -/
abbrev LeanScalarArray : UInt8 := 248
/-- `#define LeanString 249` -/
abbrev LeanString : UInt8 := 249
/-- `#define LeanMPZ 250` -/
abbrev LeanMPZ : UInt8 := 250
/-- `#define LeanThunk 251` -/
abbrev LeanThunk : UInt8 := 251
/-- `#define LeanTask 252` -/
abbrev LeanTask : UInt8 := 252
/-- `#define LeanRef 253` -/
abbrev LeanRef : UInt8 := 253
/-- `#define LeanExternal 254` -/
abbrev LeanExternal : UInt8 := 254
/-- `#define LeanReserved 255`, which no runtime object has. -/
abbrev LeanReserved : UInt8 := 255

/--
`LEAN_RC_STICKY_DROP`, read as unsigned. Once a count above zero is excluded, a count at or below it
is persistent or sticky, and releasing a reference leaves it alone.
-/
abbrev stickyDrop : UInt32 := 0xA0000000

/--
The object operations the cascade is written over, on objects `Obj` (which also cover immediates
and `NULL`) and slot cursors `Slot`. Slot counts include the slots that hold immediates.
-/
structure Ops (m : Type → Type) (Obj Slot : Type) where
  /-- Whether a value is an immediate, which holds no reference. -/
  isScalar : Obj → Bool
  /-- Whether a value is `NULL`. -/
  isNull : Obj → Bool
  /-- `NULL`, which also ends the worklist. -/
  null : Obj
  /-- The count of an object. -/
  getRc : Obj → m Int32
  /-- Decrement a count above one. -/
  decRc : Obj → m Unit
  /-- Atomically add one to a thread-shared count, returning the count it replaced. -/
  releaseMt : Obj → m Int32
  /-- Link an object that has lost its last reference to the rest of the worklist. -/
  setNext : Obj → Obj → m Unit
  /-- The worklist link of a queued object. -/
  getNext : Obj → m Obj
  /-- The kind of an object. -/
  tag : Obj → m UInt8
  /-- The first slot of a constructor. -/
  ctorObjs : Obj → m Slot
  /-- The number of slots of a constructor. -/
  ctorNumObjs : Obj → m USize
  /-- The first slot of a closure. -/
  closureFixed : Obj → m Slot
  /-- The number of slots of a closure. -/
  closureNumFixed : Obj → m USize
  /-- The first slot of an array. -/
  arrayElems : Obj → m Slot
  /-- The number of slots of an array. -/
  arraySize : Obj → m USize
  /-- The next slot. -/
  nextSlot : Slot → Slot
  /-- The value a slot holds. Reading it does not consume the reference. -/
  getSlot : Slot → m Obj
  /-- The closure of a thunk, `NULL` once it is forced. -/
  thunkClosure : Obj → m Obj
  /-- The value of a thunk, `NULL` until it is forced. -/
  thunkValue : Obj → m Obj
  /-- The value of a `Ref`, which may be `NULL`. -/
  refValue : Obj → m Obj
  /-- Free a constructor, thunk or `Ref`. -/
  freeSmall : Obj → m Unit
  /-- Free a closure. -/
  freeClosure : Obj → m Unit
  /-- Free an array. -/
  freeArray : Obj → m Unit
  /-- Free a scalar array. -/
  freeSarray : Obj → m Unit
  /-- Free a string. -/
  freeString : Obj → m Unit
  /-- Destroy and free a big number. -/
  freeMpz : Obj → m Unit
  /-- Run the finalizer of an external object and free it. -/
  freeExternal : Obj → m Unit
  /-- Hand a task to the task manager, which releases what it holds. -/
  deactivateTask : Obj → m Unit
  /-- Hand a promise to the task manager, which releases what it holds. -/
  deactivatePromise : Obj → m Unit
  /-- Abort on an object of no runtime kind. -/
  unreachable : Obj → m Unit

variable {m : Type → Type} [Monad m] {Obj Slot : Type} (A : Ops m Obj Slot)

/-
The runtime deletes objects before this module is initialized, so what `Native.cascade` runs must
not read a closed term or a module constant: the kinds and `stickyDrop` are `abbrev`s, which
compile to literals, and `Int32` literals are written `Int32.ofUInt32 n`, since `(1 : Int32)`
compiles to a closed term. `tests/misc_dir/rc_deletion/heaps.c` deletes without initializing Init.
-/

/--
Whether releasing one reference to `o`, whose count `rc` is neither above one nor one, makes this
thread responsible for deleting `o`: never for a persistent or sticky count, and for a thread-shared
count when the atomic increment replaces minus one.
-/
@[inline] def isLastShared (o : Obj) (rc : Int32) : m Bool := do
  if rc.toUInt32 ≤ stickyDrop then
    return false
  else
    return (← A.releaseMt o) == .ofUInt32 0xFFFFFFFF

/-- Queue `o` on the worklist `todo`, and return the new worklist. -/
@[inline] def push (o todo : Obj) : m Obj := do
  A.setNext o todo
  return o

/--
Release the reference that a slot of an object being deleted holds, and return the worklist.
-/
@[inline] def release (o todo : Obj) : m Obj := do
  if A.isScalar o then
    return todo
  else
    let rc ← A.getRc o
    if rc > .ofUInt32 1 then
      A.decRc o
      return todo
    else if rc == .ofUInt32 1 then
      push A o todo
    else if ← isLastShared A o rc then
      push A o todo
    else
      return todo

/-- Release the `n` slots from `it` on. -/
@[specialize A] def releaseSlots (it : Slot) (n : USize) (todo : Obj) : m Obj :=
  if h : n = 0 then
    return todo
  else do
    let todo ← release A (← A.getSlot it) todo
    releaseSlots (A.nextSlot it) (n - 1) todo
termination_by n.toNat
decreasing_by
  have hn : 0 < n.toNat :=
    Nat.pos_of_ne_zero fun e => h (USize.toNat_inj.mp (e.trans USize.toNat_zero.symm))
  have h1 : (1 : USize) ≤ n := USize.le_iff_toNat_le.mpr (by rw [USize.toNat_one]; exact hn)
  rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]
  exact Nat.sub_lt hn Nat.one_pos

/-- Delete `o`, not a constructor, by its kind `tag`, and return the worklist. -/
@[specialize A] def coreOther (o : Obj) (tag : UInt8) (todo : Obj) : m Obj := do
  if tag == LeanClosure then
    let todo ← releaseSlots A (← A.closureFixed o) (← A.closureNumFixed o) todo
    A.freeClosure o
    return todo
  else if tag == LeanArray then
    let todo ← releaseSlots A (← A.arrayElems o) (← A.arraySize o) todo
    A.freeArray o
    return todo
  else if tag == LeanScalarArray then
    A.freeSarray o
    return todo
  else if tag == LeanString then
    A.freeString o
    return todo
  else if tag == LeanMPZ then
    A.freeMpz o
    return todo
  else if tag == LeanThunk then
    let c ← A.thunkClosure o
    let todo ← (if A.isNull c then pure todo else release A c todo)
    let v ← A.thunkValue o
    let todo ← (if A.isNull v then pure todo else release A v todo)
    A.freeSmall o
    return todo
  else if tag == LeanRef then
    let v ← A.refValue o
    let todo ← (if A.isNull v then pure todo else release A v todo)
    A.freeSmall o
    return todo
  else if tag == LeanTask then
    A.deactivateTask o
    return todo
  else if tag == LeanPromise then
    A.deactivatePromise o
    return todo
  else if tag == LeanExternal then
    A.freeExternal o
    return todo
  else
    A.unreachable o
    return todo

/-- Delete `o`, and return the worklist. -/
@[inline] def core (o todo : Obj) : m Obj := do
  let tag ← A.tag o
  if tag ≤ LeanMaxCtorTag then
    let todo ← releaseSlots A (← A.ctorObjs o) (← A.ctorNumObjs o) todo
    A.freeSmall o
    return todo
  else
    coreOther A o tag todo

open scoped Lean.Order.MonadTail in
/--
Delete `o`, then the objects queued on `todo` until it is empty. Whether the loop ends depends on
the heap, so it is defined as a fixpoint.
-/
@[specialize A] def cascadeLoop [Lean.Order.MonadTail m] (o todo : Obj) : m Unit := do
  let todo ← core A o todo
  if A.isNull todo then
    return
  else
    cascadeLoop todo (← A.getNext todo)
partial_fixpoint

/--
Delete `o`, for which this thread holds deletion responsibility, and every object that thereby loses
its last reference.
-/
@[inline] def cascade [Lean.Order.MonadTail m] (o : Obj) : m Unit :=
  cascadeLoop A o A.null

end Lean.Runtime.Deletion

end

/-! ## The runtime's heap

These declarations are private: they act on raw addresses, and only the runtime calls the cascade.
-/

namespace Lean.Runtime.Deletion.Native

/-
Objects and slots are addresses. Each primitive is the function named in its `extern` attribute.
-/
@[extern "lean_del_get_rc"] opaque getRc (o : USize) : BaseIO Int32
@[extern "lean_del_dec_rc"] opaque decRc (o : USize) : BaseIO Unit
@[extern "lean_del_release_mt"] opaque releaseMt (o : USize) : BaseIO Int32
@[extern "lean_del_set_next"] opaque setNext (o next : USize) : BaseIO Unit
@[extern "lean_del_get_next"] opaque getNext (o : USize) : BaseIO USize
@[extern "lean_del_tag"] opaque tag (o : USize) : BaseIO UInt8
@[extern "lean_del_ctor_objs"] opaque ctorObjs (o : USize) : BaseIO USize
@[extern "lean_del_ctor_num_objs"] opaque ctorNumObjs (o : USize) : BaseIO USize
@[extern "lean_del_closure_fixed"] opaque closureFixed (o : USize) : BaseIO USize
@[extern "lean_del_closure_num_fixed"] opaque closureNumFixed (o : USize) : BaseIO USize
@[extern "lean_del_array_elems"] opaque arrayElems (o : USize) : BaseIO USize
@[extern "lean_del_array_size"] opaque arraySize (o : USize) : BaseIO USize
@[extern "lean_del_next_slot"] opaque nextSlot (it : USize) : USize
@[extern "lean_del_get_slot"] opaque getSlot (it : USize) : BaseIO USize
@[extern "lean_del_thunk_closure"] opaque thunkClosure (o : USize) : BaseIO USize
@[extern "lean_del_thunk_value"] opaque thunkValue (o : USize) : BaseIO USize
@[extern "lean_del_ref_value"] opaque refValue (o : USize) : BaseIO USize
@[extern "lean_del_free_small"] opaque freeSmall (o : USize) : BaseIO Unit
@[extern "lean_del_free_closure"] opaque freeClosure (o : USize) : BaseIO Unit
@[extern "lean_del_free_array"] opaque freeArray (o : USize) : BaseIO Unit
@[extern "lean_del_free_sarray"] opaque freeSarray (o : USize) : BaseIO Unit
@[extern "lean_del_free_string"] opaque freeString (o : USize) : BaseIO Unit
@[extern "lean_del_free_mpz"] opaque freeMpz (o : USize) : BaseIO Unit
@[extern "lean_del_free_external"] opaque freeExternal (o : USize) : BaseIO Unit
@[extern "lean_del_deactivate_task"] opaque deactivateTask (o : USize) : BaseIO Unit
@[extern "lean_del_deactivate_promise"] opaque deactivatePromise (o : USize) : BaseIO Unit
@[extern "lean_del_unreachable"] opaque unreachable (o : USize) : BaseIO Unit

/-- Whether a value is an immediate: its address is odd. -/
@[inline] def isScalar (o : USize) : Bool := o &&& 1 == 1

/-- Whether a value is `NULL`. -/
@[inline] def isNull (o : USize) : Bool := o == 0

/-- The object operations on the runtime's heap. -/
@[inline] def ops : Ops BaseIO USize USize where
  isScalar
  isNull
  null := 0
  getRc
  decRc
  releaseMt
  setNext
  getNext
  tag
  ctorObjs
  ctorNumObjs
  closureFixed
  closureNumFixed
  arrayElems
  arraySize
  nextSlot
  getSlot
  thunkClosure
  thunkValue
  refValue
  freeSmall
  freeClosure
  freeArray
  freeSarray
  freeString
  freeMpz
  freeExternal
  deactivateTask
  deactivatePromise
  unreachable

/--
`lean_del_cascade`, which `lean_dec_ref_cold` calls on an object whose last reference it has
released.
-/
@[export lean_del_cascade] def cascade (o : USize) : BaseIO Unit :=
  Deletion.cascade ops o

end Lean.Runtime.Deletion.Native
