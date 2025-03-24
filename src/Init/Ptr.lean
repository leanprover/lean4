/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Data.UInt.BasicAux


@[extern "lean_ptr_addr"]
unsafe opaque ptrAddrUnsafe {α : Type u} (a : @& α) : USize

/--
Returns `true` if `a` is an exclusive object.
We say an object is exclusive if it is single-threaded and its reference counter is 1.
-/
@[extern "lean_is_exclusive_obj"]
unsafe opaque isExclusiveUnsafe {α : Type u} (a : @& α) : Bool

set_option linter.unusedVariables.funArgs false in
@[inline] unsafe def withPtrAddrUnsafe {α : Type u} {β : Type v} (a : α) (k : USize → β) (h : ∀ u₁ u₂, k u₁ = k u₂) : β :=
  k (ptrAddrUnsafe a)

@[inline] unsafe def ptrEq (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

unsafe def ptrEqList : (as bs : List α) → Bool
  | .nil, .nil => true
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
