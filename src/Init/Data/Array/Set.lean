/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Tactics


/--
Set an element in an array, using a proof that the index is in bounds.
(This proof can usually be omitted, and will be synthesized automatically.)

This will perform the update destructively provided that `a` has a reference
count of 1 when called.
-/
@[extern "lean_array_fset"]
def Array.set (a : Array α) (i : @& Nat) (v : α) (h : i < a.size := by get_elem_tactic) :
    Array α where
  toList := a.toList.set i v

/--
Set an element in an array, or do nothing if the index is out of bounds.

This will perform the update destructively provided that `a` has a reference
count of 1 when called.
-/
@[inline] def Array.setD (a : Array α) (i : Nat) (v : α) : Array α :=
  dite (LT.lt i a.size) (fun h => a.set i v h) (fun _ => a)

/--
Set an element in an array, or panic if the index is out of bounds.

This will perform the update destructively provided that `a` has a reference
count of 1 when called.
-/
@[extern "lean_array_set"]
def Array.set! (a : Array α) (i : @& Nat) (v : α) : Array α :=
  Array.setD a i v
