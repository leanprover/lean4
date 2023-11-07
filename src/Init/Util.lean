/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.ToString.Basic

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
def dbgTraceIfShared {α : Type u} (s : String) (a : α) : α := a

/-- Print stack trace to stderr before evaluating given closure. Currently supported on Linux only. -/
@[never_extract, extern "lean_dbg_stack_trace"]
def dbgStackTrace {α : Type u} (f : Unit → α) : α := f ()

@[extern "lean_dbg_sleep"]
def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α := f ()

@[noinline] private def mkPanicMessage (modName : String) (line col : Nat) (msg : String) : String :=
  "PANIC at " ++ modName ++ ":" ++ toString line ++ ":" ++ toString col ++ ": " ++ msg

@[never_extract, inline] def panicWithPos {α : Type u} [Inhabited α] (modName : String) (line col : Nat) (msg : String) : α :=
  panic (mkPanicMessage modName line col msg)

@[noinline] private def mkPanicMessageWithDecl (modName : String) (declName : String) (line col : Nat) (msg : String) : String :=
  "PANIC at " ++ declName ++ " " ++ modName ++ ":" ++ toString line ++ ":" ++ toString col ++ ": " ++ msg

@[never_extract, inline] def panicWithPosWithDecl {α : Type u} [Inhabited α] (modName : String) (declName : String) (line col : Nat) (msg : String) : α :=
  panic (mkPanicMessageWithDecl modName declName line col msg)

@[extern "lean_ptr_addr"]
unsafe opaque ptrAddrUnsafe {α : Type u} (a : @& α) : USize

set_option linter.unusedVariables.funArgs false in
@[inline] unsafe def withPtrAddrUnsafe {α : Type u} {β : Type v} (a : α) (k : USize → β) (h : ∀ u₁ u₂, k u₁ = k u₂) : β :=
  k (ptrAddrUnsafe a)

@[inline] unsafe def ptrEq (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

unsafe def ptrEqList : (as bs : List α) → Bool
  | [], [] => true
  | a::as, b::bs => if ptrEq a b then ptrEqList as bs else false
  | _, _ => false

set_option linter.unusedVariables.funArgs false in
@[inline] unsafe def withPtrEqUnsafe {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool :=
  if ptrEq a b then true else k ()

@[implemented_by withPtrEqUnsafe]
def withPtrEq {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool := k ()

/-- `withPtrEq` for `DecidableEq` -/
@[inline] def withPtrEqDecEq {α : Type u} (a b : α) (k : Unit → Decidable (a = b)) : Decidable (a = b) :=
  let b := withPtrEq a b (fun _ => toBoolUsing (k ())) (toBoolUsing_eq_true (k ()));
  match h:b with
  | true  => isTrue (ofBoolUsing_eq_true h)
  | false => isFalse (ofBoolUsing_eq_false h)

@[implemented_by withPtrAddrUnsafe]
def withPtrAddr {α : Type u} {β : Type v} (a : α) (k : USize → β) (h : ∀ u₁ u₂, k u₁ = k u₂) : β := k 0

@[never_extract]
private def outOfBounds [Inhabited α] : α :=
  panic! "index out of bounds"

@[inline] def getElem! [GetElem cont idx elem dom] [Inhabited elem] (xs : cont) (i : idx) [Decidable (dom xs i)] : elem :=
  if h : _ then getElem xs i h else outOfBounds

@[inline] def getElem? [GetElem cont idx elem dom] (xs : cont) (i : idx) [Decidable (dom xs i)] : Option elem :=
  if h : _ then some (getElem xs i h) else none

macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)
macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)

/--
  Marks given value and its object graph closure as multi-threaded if currently
  marked single-threaded. This will make reference counter updates atomic and
  thus more costly. It can still be useful to do eagerly when the value will be
  shared between threads later anyway and there is available time budget to mark
  it now. -/
@[extern "lean_runtime_mark_multi_threaded"]
def Runtime.markMultiThreaded (a : α) : α := a

/--
  Marks given value and its object graph closure as persistent. This will remove
  reference counter updates but prevent the closure from being deallocated until
  the end of the process! It can still be useful to do eagerly when the value
  will be marked persistent later anyway and there is available time budget to
  mark it now or it would be unnecessarily marked multi-threaded in between. -/
@[extern "lean_runtime_mark_persistent"]
def Runtime.markPersistent (a : α) : α := a
