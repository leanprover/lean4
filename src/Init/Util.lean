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
@[neverExtract, extern "lean_dbg_trace"]
def dbgTrace {α : Type u} (s : String) (f : Unit → α) : α := f ()

def dbgTraceVal {α : Type u} [ToString α] (a : α) : α :=
  dbgTrace (toString a) (fun _ => a)

set_option linter.unusedVariables.funArgs false in
/-- Display the given message if `a` is shared, that is, RC(a) > 1 -/
@[neverExtract, extern "lean_dbg_trace_if_shared"]
def dbgTraceIfShared {α : Type u} (s : String) (a : α) : α := a

@[extern "lean_dbg_sleep"]
def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α := f ()

@[noinline] private def mkPanicMessage (modName : String) (line col : Nat) (msg : String) : String :=
  "PANIC at " ++ modName ++ ":" ++ toString line ++ ":" ++ toString col ++ ": " ++ msg

@[neverExtract, inline] def panicWithPos {α : Type u} [Inhabited α] (modName : String) (line col : Nat) (msg : String) : α :=
  panic (mkPanicMessage modName line col msg)

@[noinline] private def mkPanicMessageWithDecl (modName : String) (declName : String) (line col : Nat) (msg : String) : String :=
  "PANIC at " ++ declName ++ " " ++ modName ++ ":" ++ toString line ++ ":" ++ toString col ++ ": " ++ msg

@[neverExtract, inline] def panicWithPosWithDecl {α : Type u} [Inhabited α] (modName : String) (declName : String) (line col : Nat) (msg : String) : α :=
  panic (mkPanicMessageWithDecl modName declName line col msg)

/-!

# The unsoundness of `ptrAddr`

Reference: [Sealing Pointer-Based Optimizations Behind Pure Functions](https://arxiv.org/pdf/2003.01685.pdf)

Note that we can not allow bare reference-equality in trusted Lean code.
To see why, let `α` be `List String` and define `x` and `y` as follows:

```lean
def x := ["hello"]
def y := x.map id

#eval ptrEq x y -- false
#eval x = y     -- true
```

Suppose that `ptrEq` was a safe definition (call it `evilEq`), then using definition of equality in Lean we can derive:

```
@[implementedBy ptrEq]
opaque evilEq {α : Type u} (a b : α) : Bool

theorem evil {α} : ∀ {a b : α}, (a = b) → (evilEq a b) = (evilEq a a)
  | _, _, rfl => rfl

#eval (evilEq x y) = (evilEq x x) -- false!
```

But now the evaluation of `(evilEq x y) = (evilEq x x)` contradicts the `evil` theorem!

To create the sound version of `ptrEq` called `withPtrEq`, we have to provide the hypothesis `h : a = b → k() = true`,
since now if the values are not pointer-equal, it will run the decision procedure `k` instead.
-/

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

/-- If `a` and `b` are reference-equal (that is, their pointers point to the same address), then return `true`, otherwise return `k()`.
`h` demands that `k` should be a decision procedure that returns `true` whenever `a = b`.

This function allows us to implement safe functions that compare `a` and `b`, with an optimisation for when `a` is reference-equal to `b`.  -/
@[implementedBy withPtrEqUnsafe]
def withPtrEq {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool := k ()

/-- `withPtrEq` for `DecidableEq` -/
@[inline] def withPtrEqDecEq {α : Type u} (a b : α) (k : Unit → Decidable (a = b)) : Decidable (a = b) :=
  let b := withPtrEq a b (fun _ => toBoolUsing (k ())) (toBoolUsing_eq_true (k ()));
  match h:b with
  | true  => isTrue (ofBoolUsing_eq_true h)
  | false => isFalse (ofBoolUsing_eq_false h)

@[implementedBy withPtrAddrUnsafe]
def withPtrAddr {α : Type u} {β : Type v} (a : α) (k : USize → β) (h : ∀ u₁ u₂, k u₁ = k u₂) : β := k 0

@[inline] def getElem! [GetElem cont idx elem dom] [Inhabited elem] (xs : cont) (i : idx) [Decidable (dom xs i)] : elem :=
  if h : _ then getElem xs i h else panic! "index out of bounds"

@[inline] def getElem? [GetElem cont idx elem dom] (xs : cont) (i : idx) [Decidable (dom xs i)] : Option elem :=
  if h : _ then some (getElem xs i h) else none

macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)
macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)
