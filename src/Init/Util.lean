/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.ToString

universes u v
/- debugging helper functions -/
@[neverExtract, extern "lean_dbg_trace"]
def dbgTrace {α : Type u} (s : String) (f : Unit → α) : α :=
f ()

/- Display the given message if `a` is shared, that is, RC(a) > 1 -/
@[neverExtract, extern "lean_dbg_trace_if_shared"]
def dbgTraceIfShared {α : Type u} (s : String) (a : α) : α :=
a

@[extern "lean_dbg_sleep"]
def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α :=
f ()

@[extern c inline "#4"]
unsafe def unsafeCast {α : Type u} {β : Type v} [inh : @& Inhabited β] (a : α) : β := arbitrary _

@[neverExtract, extern "lean_panic_fn"]
constant panic {α : Type u} [Inhabited α] (msg : String) : α := arbitrary _

@[noinline] private def mkPanicMessage (modName : String) (line col : Nat) (msg : String) : String :=
"PANIC at " ++ modName ++ ":" ++ toString line ++ ":" ++ toString col ++ ": " ++ msg

@[neverExtract, inline] def panicWithPos {α : Type u} [Inhabited α] (modName : String) (line col : Nat) (msg : String) : α :=
panic (mkPanicMessage modName line col msg)

-- TODO: should be a macro
@[neverExtract, noinline, nospecialize] def unreachable! {α : Type u} [Inhabited α] : α :=
panic! "unreachable"

@[extern "lean_ptr_addr"]
unsafe def ptrAddrUnsafe {α : Type u} (a : @& α) : USize := 0

@[inline] unsafe def withPtrAddrUnsafe {α : Type u} {β : Type v} (a : α) (k : USize → β) (h : ∀ u₁ u₂, k u₁ = k u₂) : β :=
k (ptrAddrUnsafe a)

@[inline] unsafe def withPtrEqUnsafe {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool :=
if ptrAddrUnsafe a == ptrAddrUnsafe b then true else k ()

inductive PtrEqResult {α : Type u} (x y : α) : Type
| unknown {}          : PtrEqResult
| yes     (h : x = y) : PtrEqResult

@[inline] unsafe def withPtrEqResultUnsafe {α : Type u} {β : Type v} [Subsingleton β] (a b : α) (k : PtrEqResult a b → β) : β :=
if ptrAddrUnsafe a == ptrAddrUnsafe b then k (PtrEqResult.yes lcProof) else k PtrEqResult.unknown

@[implementedBy withPtrEqUnsafe]
def withPtrEq {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool :=
k ()

/-- `withPtrEq` for `DecidableEq` -/
@[inline] def withPtrEqDecEq {α : Type u} (a b : α) (k : Unit → Decidable (a = b)) : Decidable (a = b) :=
let b := withPtrEq a b (fun _ => toBoolUsing (k ())) (toBoolUsingEqTrue (k ()));
condEq b
  (fun h => isTrue (ofBoolUsingEqTrue h))
  (fun h => isFalse (ofBoolUsingEqFalse h))

/-- Similar to `withPtrEq`, but executes the continuation `k` with the "result" of the pointer equality test. -/
@[implementedBy withPtrEqResultUnsafe]
def withPtrEqResult {α : Type u} {β : Type v} [Subsingleton β] (a b : α) (k : PtrEqResult a b → β) : β :=
k PtrEqResult.unknown

@[implementedBy withPtrAddrUnsafe]
def withPtrAddr {α : Type u} {β : Type v} (a : α) (k : USize → β) (h : ∀ u₁ u₂, k u₁ = k u₂) : β :=
k 0
