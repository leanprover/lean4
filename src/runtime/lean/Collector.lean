/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

prelude
public import Init
public import Init.Internal.Order.MonadTail

/-!
Reference-counting deletion, compiled to `runtime/object_gc.inc`.

The complete entry point also runs in the pure graph interpreter in `tests/misc_dir/rc_graph`.
The native specialization uses only machine integers and erased `BaseIO` state. Raw pointers are
borrowed addresses, never Lean-owned references. The generator checks the reachable compiler IR
before emitting code without module initializers or boxed entry points.
-/

namespace Lean.Runtime.GC

open scoped Lean.Order.MonadTail

/--
Return whether releasing one reference acquired exclusive responsibility for deletion.
The shared transition is decided by the value returned from the atomic operation.
-/
@[always_inline] public def releaseLast [Monad m] (read : m Int32)
    (write : Int32 → m Unit) (fetchAdd : m Int32) : m Bool := do
  let rc ← read
  if rc > Int32.ofUInt32 1 then
    write (rc - Int32.ofUInt32 1)
    return false
  else if rc == Int32.ofUInt32 1 then
    return true
  else
    let sharedRC ← read
    if sharedRC == Int32.ofUInt32 0 || sharedRC ≤ Int32.ofUInt32 0xA0000000 then -- LEAN_RC_STICKY_DROP
      return false
    else
      return (← fetchAdd) == Int32.ofUInt32 0xFFFFFFFF

/--
Memory and representation operations. `releaseLast` interprets the shared counter transition above.
`work o` views the list whose head is `o`; `writeNext o todo` must establish its tail first.
The native view is just the address; the finite interpreter reads the saved tail.
-/
public structure Adapter (m : Type → Type) (Reference Object Cursor Work : Type) where
  isIgnored : Reference → Bool
  object : Reference → Object
  releaseLast : Reference → m Bool
  writeNext : Object → Work → m Unit
  work : Object → m Work
  readTag : Object → m UInt8
  fieldCount : Object → UInt8 → m USize
  fieldBegin : Object → UInt8 → m Cursor
  fieldNext : Cursor → Cursor
  readField : Cursor → m Reference
  readThunkClosure : Object → m Reference
  readThunkValue : Object → m Reference
  dispose : Object → UInt8 → m Unit
  empty : Work
  isEmpty : Work → Bool
  head : Work → Object
  tail : Work → m Work

/-- Runtime tags 247 and 255 have no deletion layout. -/
public inductive ObjectKind where
  | ctor | promise | closure | array | scalarArray | string | mpz | thunk | task | ref | external
  | invalid
  deriving DecidableEq

/-- Keep classification shared through Lean lowering; the native compiler can inline it. -/
@[noinline] public def classify (tag : UInt8) : ObjectKind :=
  if tag ≤ 243 then .ctor else
  match tag with
  | 244 => .promise
  | 245 => .closure
  | 246 => .array
  | 248 => .scalarArray
  | 249 => .string
  | 250 => .mpz
  | 251 => .thunk
  | 252 => .task
  | 253 => .ref
  | 254 => .external
  | _ => .invalid

/--
Typed layout access and terminal memory effects. Counts include null and immediate slots.
Finalizers and MPZ destructors run while their storage is live; freeing follows in `dispose`.
-/
public structure Primitives (m : Type → Type) (Object Cursor : Type) where
  ctorCount : Object → m USize
  ctorBegin : Object → m Cursor
  closureCount : Object → m USize
  closureBegin : Object → m Cursor
  arrayCount : Object → m USize
  arrayBegin : Object → m Cursor
  refBegin : Object → m Cursor
  emptyCursor : Cursor
  freeSmall : Object → m Unit
  freeClosure : Object → m Unit
  freeArray : Object → m Unit
  freeScalarArray : Object → m Unit
  freeString : Object → m Unit
  destroyMPZ : Object → m Unit
  deactivateTask : Object → m Unit
  deactivatePromise : Object → m Unit
  finalizeExternal : Object → m Unit
  unreachable : Object → m Unit

@[always_inline] public def fieldCount [Monad m] (p : Primitives m Object Cursor)
    (o : Object) (tag : UInt8) : m USize :=
  match classify tag with
  | .ctor => p.ctorCount o
  | .closure => p.closureCount o
  | .array => p.arrayCount o
  | .ref => pure 1
  | _ => pure 0

@[always_inline] public def fieldBegin [Monad m] (p : Primitives m Object Cursor)
    (o : Object) (tag : UInt8) : m Cursor :=
  match classify tag with
  | .ctor => p.ctorBegin o
  | .closure => p.closureBegin o
  | .array => p.arrayBegin o
  | .ref => p.refBegin o
  | _ => pure p.emptyCursor

@[always_inline] public def dispose [Monad m] (p : Primitives m Object Cursor)
    (o : Object) (tag : UInt8) : m Unit :=
  match classify tag with
  | .ctor | .thunk | .ref => p.freeSmall o
  | .closure => p.freeClosure o
  | .array => p.freeArray o
  | .scalarArray => p.freeScalarArray o
  | .string => p.freeString o
  | .mpz => do p.destroyMPZ o; p.freeSmall o
  | .task => p.deactivateTask o
  | .promise => p.deactivatePromise o
  | .external => do p.finalizeExternal o; p.freeSmall o
  | .invalid => p.unreachable o

/--
Release a field reference, saving the old head before returning the newly queued object.
Specialize the adapter before inlining to keep scanner and thunk branches compact.
-/
@[specialize a] public def release [Monad m] (a : Adapter m Reference Object Cursor Work)
    (r : Reference) (todo : Work) : m Work := do
  if a.isIgnored r then
    return todo
  else if ← a.releaseLast r then
    let o := a.object r
    a.writeNext o todo
    a.work o
  else
    return todo

@[always_inline] public def releaseField [Monad m] (a : Adapter m Reference Object Cursor Work)
    (cursor : Cursor) (todo : Work) : m Work := do
  release a (← a.readField cursor) todo

/-- Scan exactly `remaining` field occurrences, in cursor order. -/
@[specialize] public def scan [Monad m] (next : Cursor → Cursor)
    (release : Cursor → Work → m Work) (remaining : USize) (cursor : Cursor) (todo : Work) :
    m Work :=
  if h : remaining = 0 then
    pure todo
  else do
    let todo ← release cursor todo
    scan next release (remaining - 1) (next cursor) todo
termination_by remaining.toNat
decreasing_by
  have hp : 0 < remaining.toNat := by
    simp only [← USize.toNat_inj, USize.toNat_zero] at h
    omega
  rw [USize.toNat_sub_of_le]
  · simp only [USize.toNat_one]
    omega
  · apply USize.le_iff_toNat_le.mpr
    simp only [USize.toNat_one]
    omega

/-- A source remains allocated until all of its field occurrences have been released. -/
@[always_inline] public def visit [Monad m] (next : Cursor → Cursor)
    (release : Cursor → Work → m Work) (dispose : Work → m Work)
    (remaining : USize) (cursor : Cursor) (todo : Work) : m Work := do
  let todo ← scan next release remaining cursor todo
  dispose todo

@[always_inline] public def finish [Monad m] (a : Adapter m Reference Object Cursor Work)
    (o : Object) (tag : UInt8) (todo : Work) : m Work := do
  a.dispose o tag
  return todo

/-- Read a thunk's atomic closure before its cached value, then dispose its storage. -/
@[inline] public def visitThunk [Monad m] (a : Adapter m Reference Object Cursor Work)
    (o : Object) (todo : Work) : m Work := do
  let todo ← release a (← a.readThunkClosure o) todo
  let todo ← release a (← a.readThunkValue o) todo
  finish a o 251 todo

/--
Drain a LIFO worklist, continuing directly into a constructor's single child when its last reference
is released. Other children are queued; their links are read before visiting and freeing them.
Under a valid finite layout, the pure interpreter proves this fixpoint equal to the terminating
ownership collector.
-/
@[specialize a] public def loop [Monad m] [Lean.Order.MonadTail m] [Nonempty Work]
    (a : Adapter m Reference Object Cursor Work) (o : Object) (todo : Work) : m Work := do
  let resume := fun todo => do
    if a.isEmpty todo then
      pure todo
    else
      let next ← a.tail todo
      loop a (a.head todo) next
  let tag ← a.readTag o
  if tag == 251 then -- LeanThunk
    resume (← visitThunk a o todo)
  else
    let n ← a.fieldCount o tag
    let first ← a.fieldBegin o tag
    if n == 1 && tag ≤ 243 then -- LeanMaxCtorTag
      let r ← a.readField first
      if a.isIgnored r then
        resume (← finish a o tag todo)
      else if ← a.releaseLast r then
        a.dispose o tag
        loop a (a.object r) todo
      else
        resume (← finish a o tag todo)
    else
      resume (← visit a.fieldNext (releaseField a) (finish a o tag) n first todo)
partial_fixpoint

/-- A cold root release starts a fresh cascade only after acquiring deletion responsibility. -/
@[always_inline] public def decRefCold [Monad m] [Lean.Order.MonadTail m] [Nonempty Work]
    (a : Adapter m Reference Object Cursor Work) (r : Reference) : m Work := do
  if ← a.releaseLast r then
    loop a (a.object r) a.empty
  else
    return a.empty

namespace Native
public section

@[extern "lean_gc_read_rc"] opaque readRC (o : USize) : BaseIO Int32
@[extern "lean_gc_write_rc"] opaque writeRC (o : USize) (rc : Int32) : BaseIO Unit
@[extern "lean_gc_fetch_add_rc"] opaque fetchAddRC (o : USize) : BaseIO Int32
@[extern "lean_gc_read_next"] opaque readNext (o : USize) : BaseIO USize
@[extern "lean_gc_write_next"] opaque writeNext (o next : USize) : BaseIO Unit
@[extern "lean_gc_read_tag"] opaque readTag (o : USize) : BaseIO UInt8
@[extern "lean_gc_ctor_count"] opaque ctorCount (o : USize) : BaseIO USize
@[extern "lean_gc_ctor_begin"] opaque ctorBegin (o : USize) : BaseIO USize
@[extern "lean_gc_closure_count"] opaque closureCount (o : USize) : BaseIO USize
@[extern "lean_gc_closure_begin"] opaque closureBegin (o : USize) : BaseIO USize
@[extern "lean_gc_array_count"] opaque arrayCount (o : USize) : BaseIO USize
@[extern "lean_gc_array_begin"] opaque arrayBegin (o : USize) : BaseIO USize
@[extern "lean_gc_ref_begin"] opaque refBegin (o : USize) : BaseIO USize
@[extern "lean_gc_field_next"] opaque fieldNext (cursor : USize) : USize
@[extern "lean_gc_read_field"] opaque readField (cursor : USize) : BaseIO USize
@[extern "lean_gc_read_thunk_closure"] opaque readThunkClosure (o : USize) : BaseIO USize
@[extern "lean_gc_read_thunk_value"] opaque readThunkValue (o : USize) : BaseIO USize
@[extern "lean_gc_free_small"] opaque freeSmall (o : USize) : BaseIO Unit
@[extern "lean_gc_free_closure"] opaque freeClosure (o : USize) : BaseIO Unit
@[extern "lean_gc_free_array"] opaque freeArray (o : USize) : BaseIO Unit
@[extern "lean_gc_free_scalar_array"] opaque freeScalarArray (o : USize) : BaseIO Unit
@[extern "lean_gc_free_string"] opaque freeString (o : USize) : BaseIO Unit
@[extern "lean_gc_destroy_mpz"] opaque destroyMPZ (o : USize) : BaseIO Unit
@[extern "lean_gc_deactivate_task"] opaque deactivateTask (o : USize) : BaseIO Unit
@[extern "lean_gc_deactivate_promise"] opaque deactivatePromise (o : USize) : BaseIO Unit
@[extern "lean_gc_finalize_external"] opaque finalizeExternal (o : USize) : BaseIO Unit
@[extern "lean_gc_unreachable"] opaque unreachable (o : USize) : BaseIO Unit

@[always_inline] def primitives : Primitives BaseIO USize USize :=
  { ctorCount, ctorBegin, closureCount, closureBegin, arrayCount, arrayBegin, refBegin
    emptyCursor := 0
    freeSmall, freeClosure, freeArray, freeScalarArray, freeString, destroyMPZ
    deactivateTask, deactivatePromise, finalizeExternal, unreachable }

@[always_inline] def fieldCount (o : USize) (tag : UInt8) : BaseIO USize :=
  Lean.Runtime.GC.fieldCount primitives o tag

@[always_inline] def fieldBegin (o : USize) (tag : UInt8) : BaseIO USize :=
  Lean.Runtime.GC.fieldBegin primitives o tag

@[always_inline] def dispose (o : USize) (tag : UInt8) : BaseIO Unit :=
  Lean.Runtime.GC.dispose primitives o tag

@[always_inline] def adapter : Adapter BaseIO USize USize USize USize :=
  { isIgnored := fun o => o &&& 1 != 0 || o == 0
    object := id
    releaseLast := fun o => releaseLast (readRC o) (writeRC o) (fetchAddRC o)
    writeNext, work := pure, readTag, fieldCount, fieldBegin, fieldNext, readField
    readThunkClosure, readThunkValue, dispose
    empty := 0, isEmpty := (· == 0), head := id, tail := readNext }

@[export lean_gc_dec_ref_cold] def decRefCold (o : USize) : BaseIO Unit := do
  let _ ← Lean.Runtime.GC.decRefCold adapter o

end
end Native
end Lean.Runtime.GC
