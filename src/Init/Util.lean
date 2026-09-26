/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.ToString.Basic

public section

universe u v

/-! # Debugging helper functions -/

set_option linter.unusedVariables.funArgs false in
@[never_extract, extern "lean_dbg_trace"]
def dbgTrace {α : Type u} (s : String) (f : Unit → α) : α := f ()

def dbgTraceVal {α : Type u} [ToString α] (a : α) : α :=
  dbgTrace (toString a) (fun _ => a)

set_option linter.unusedVariables.funArgs false in
/-- Display the given message if `a` is shared, that is, RC(a) > 1 -/
@[never_extract, extern "lean_dbg_trace_if_shared"]
def dbgTraceIfShared {α : Type u} (s : @& String) (a : α) : α := a

/-- Print stack trace to stderr before evaluating given closure. Currently supported on Linux only. -/
@[never_extract, extern "lean_dbg_stack_trace"]
def dbgStackTrace {α : Type u} (f : Unit → α) : α := f ()

/--
Print stack trace to stderr before evaluating given closure if `cond` is true.
Currently supported on Linux only.
-/
@[never_extract]
def dbgStackTraceIf {α : Type u} (cond : Bool) (f : Unit → α) : α :=
  if cond then dbgStackTrace f else f ()

@[extern "lean_dbg_sleep"]
def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α := f ()

@[noinline] def mkPanicMessage (modName : String) (line col : Nat) (msg : String) : String :=
  String.Internal.append
    (String.Internal.append
      (String.Internal.append
        (String.Internal.append
          (String.Internal.append
            (String.Internal.append
              (String.Internal.append "PANIC at " modName)
              ":")
            (toString line))
          ":")
        (toString col))
      ": ")
    msg

@[never_extract, inline, expose] def panicWithPos {α : Sort u} [Inhabited α] (modName : String) (line col : Nat) (msg : String) : α :=
  panic (mkPanicMessage modName line col msg)

@[noinline, expose] def mkPanicMessageWithDecl (modName : String) (declName : String) (line col : Nat) (msg : String) : String :=
  String.Internal.append
    (String.Internal.append
      (String.Internal.append
        (String.Internal.append
          (String.Internal.append
            (String.Internal.append
              (String.Internal.append
                (String.Internal.append
                  (String.Internal.append "PANIC at " declName)
                  " ")
                modName)
              ":")
            (toString line))
          ":")
        (toString col))
      ": ")
    msg

@[never_extract, inline, expose] def panicWithPosWithDecl {α : Sort u} [Inhabited α] (modName : String) (declName : String) (line col : Nat) (msg : String) : α :=
  panic (mkPanicMessageWithDecl modName declName line col msg)

/--
Returns the address at which an object is allocated.

This function is unsafe because it can distinguish between definitionally equal values.
-/
@[extern "lean_ptr_addr"]
unsafe opaque ptrAddrUnsafe {α : Type u} (a : @& α) : USize

/--
Returns `true` if `a` is an exclusive object.

An object is exclusive if it is single-threaded and its reference counter is 1. This function is
unsafe because it can distinguish between definitionally equal values.
-/
@[extern "lean_is_exclusive_obj"]
unsafe opaque isExclusiveUnsafe {α : Type u} (a : @& α) : Bool

set_option linter.unusedVariables.funArgs false in
@[inline] unsafe def withPtrAddrUnsafe {α : Type u} {β : Type v} (a : α) (k : USize → β) (h : ∀ u₁ u₂, k u₁ = k u₂) : β :=
  k (ptrAddrUnsafe a)

/--
Compares two objects for pointer equality.

Two objects are pointer-equal if, at runtime, they are allocated at exactly the same address. This
function is unsafe because it can distinguish between definitionally equal values.
-/
@[inline] unsafe def ptrEq (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/--
Compares two lists of objects for element-wise pointer equality. Returns `true` if both lists are
the same length and the objects at the corresponding indices of each list are pointer-equal.

Two objects are pointer-equal if, at runtime, they are allocated at exactly the same address. This
function is unsafe because it can distinguish between definitionally equal values.
-/
unsafe def ptrEqList : (as bs : List α) → Bool
  | [], [] => true
  | a::as, b::bs => if ptrEq a b then ptrEqList as bs else false
  | _, _ => false

/--
Returns `true` if `a` and `b` are represented by the same pointer at runtime, or `k ()` otherwise.

If `k` is a function that performs an equality check on `a` and `b`, then this operation can be
used to short-circuit the equality check for pointer-equal input.

This cannot be wrapped into a safe operation with logical value `k ()` because that would be
unsound if `α` includes computationally irrelevant data like types. Consider the example
`α := Prop`, `a := True`, `b := False`, `k := fun _ => false`. In this case, `a = b → k () = true`
is true, but `a` and `b` have the same runtime representation of an erased type, so `ptrEq a b` is
true and this function returns `true`, even though `k ()` is `false`.

Users who require a safe version of this function whose logical model is equal to `k ()` must
manually check that for their type pointer-equality implies logical equality and then create a
specialized version of this function using `implemented_by`:

```lean
namespace MyType

@[inline]
unsafe def withPtrEqUnsafe (a b : MyType) (k : Unit → Bool) (h : a = b → k () = true) : Bool :=
  _root_.withPtrEqUnsafe a b k h

-- Safety: `MyType` contains no non-subsingleton erased data
@[implemented_by withPtrEqUnsafe]
def withPtrEq (a b : MyType) (k : Unit → Bool) (_h : a = b → k () = true) : Bool :=
  k ()

end MyType
```
-/
@[inline] unsafe def withPtrEqUnsafe {α : Type u} (a b : α) (k : Unit → Bool) (_h : a = b → k () = true) : Bool :=
  if ptrEq a b then true else k ()

@[deprecated "See the docstring of `withPtrEqUnsafe`" (since := "2026-09-21")]
unsafe def withPtrEq {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool :=
  withPtrEqUnsafe a b k h

/--
Build a `DecidableEq` instance that short-circuits using `withPtrEq` where possible.
Since the general-purpose `withPtrEqUnsafe` is unsafe, users need to provide their own `withPtrEq`
function; see the comment on `withPtrEqUnsafe`.
-/
@[inline] def withPtrEqDecEq {α : Type u}
    (withPtrEq : (a b : α) → (k : Unit → Bool) → (h : a = b → k () = true) → Bool)
    (hw : ∀ a b k h, withPtrEq a b k h = k ())
    (a b : α) (k : Unit → Decidable (a = b)) : Decidable (a = b) where
  decide := withPtrEq a b (fun _ => toBoolUsing (k ())) (toBoolUsing_eq_true (k ()))
  reflects_decide := by simpa [hw] using reflects_toBoolUsing

@[implemented_by withPtrAddrUnsafe]
def withPtrAddr {α : Type u} {β : Type v} (a : α) (k : USize → β) (h : ∀ u₁ u₂, k u₁ = k u₂) : β := k 0

set_option linter.unusedVariables.funArgs false in
@[inline] unsafe def withIsExclusiveUnsafe {α : Type u} {β : Type v} (a : @& α) (k : Bool → β)
    (h : k true = k false) : β :=
  k (isExclusiveUnsafe a)

/--
Checks whether `a` is exclusive at runtime, applying `k` to the verdict. This can be used, for
example, to skip caching values that are not referenced from anywhere else. This function is
safe because of the proof obligation `h`, which ensures that the result does not depend on the
answer.
 
This function is a safe wrapper around `isExclusive`. Logically, it is `k false`. 

Being exclusive does not imply that `a` can be updated in place: that also requires the caller
to own `a` rather than borrow it.
-/
@[implemented_by withIsExclusiveUnsafe]
def withIsExclusive {α : Type u} {β : Type v} (a : @& α) (k : Bool → β) (h : k true = k false) : β :=
  k false
