import Collector

/-!
Check the shared field-layout and disposal dispatch for every byte tag and arbitrary primitives.
Native binding equalities separately check which opaque primitive declarations are selected.
-/

namespace Lean.Runtime.GC

private def expectedKind (tag : Nat) : ObjectKind :=
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

set_option maxRecDepth 2048 in
theorem classify_refines (tag : UInt8) : classify tag = expectedKind tag.toNat := by
  have exhaustive : ∀ n : Fin UInt8.size,
      classify (UInt8.ofNat n.val) = expectedKind n.val := by decide
  simpa using exhaustive tag.toFin

theorem field_count_dispatch_refines [Monad m] (p : Primitives m Object Cursor)
    (o : Object) (tag : UInt8) :
    fieldCount p o tag =
      match expectedKind tag.toNat with
      | .ctor => p.ctorCount o
      | .closure => p.closureCount o
      | .array => p.arrayCount o
      | .ref => pure 1
      | _ => pure 0 := by
  simp only [fieldCount, classify_refines]
  cases expectedKind tag.toNat <;> rfl

theorem field_begin_dispatch_refines [Monad m] (p : Primitives m Object Cursor)
    (o : Object) (tag : UInt8) :
    fieldBegin p o tag =
      match expectedKind tag.toNat with
      | .ctor => p.ctorBegin o
      | .closure => p.closureBegin o
      | .array => p.arrayBegin o
      | .ref => p.refBegin o
      | _ => pure p.emptyCursor := by
  simp only [fieldBegin, classify_refines]
  cases expectedKind tag.toNat <;> rfl

theorem dispose_dispatch_refines [Monad m] (p : Primitives m Object Cursor)
    (o : Object) (tag : UInt8) :
    dispose p o tag =
      match expectedKind tag.toNat with
      | .ctor | .thunk | .ref => p.freeSmall o
      | .closure => p.freeClosure o
      | .array => p.freeArray o
      | .scalarArray => p.freeScalarArray o
      | .string => p.freeString o
      | .mpz => do p.destroyMPZ o; p.freeSmall o
      | .task => p.deactivateTask o
      | .promise => p.deactivatePromise o
      | .external => do p.finalizeExternal o; p.freeSmall o
      | .invalid => p.unreachable o := by
  simp only [dispose, classify_refines]
  cases expectedKind tag.toNat <;> rfl

private def nativePrimitives : Primitives BaseIO USize USize :=
  { ctorCount := Native.ctorCount, ctorBegin := Native.ctorBegin
    closureCount := Native.closureCount, closureBegin := Native.closureBegin
    arrayCount := Native.arrayCount, arrayBegin := Native.arrayBegin
    refBegin := Native.refBegin, emptyCursor := 0
    freeSmall := Native.freeSmall, freeClosure := Native.freeClosure
    freeArray := Native.freeArray, freeScalarArray := Native.freeScalarArray
    freeString := Native.freeString, destroyMPZ := Native.destroyMPZ
    deactivateTask := Native.deactivateTask, deactivatePromise := Native.deactivatePromise
    finalizeExternal := Native.finalizeExternal, unreachable := Native.unreachable }

theorem native_dispatch_uses_shared (o : USize) (tag : UInt8) :
    Native.fieldCount o tag = fieldCount nativePrimitives o tag ∧
    Native.fieldBegin o tag = fieldBegin nativePrimitives o tag ∧
    Native.dispose o tag = dispose nativePrimitives o tag := by
  exact ⟨rfl, rfl, rfl⟩

end Lean.Runtime.GC
