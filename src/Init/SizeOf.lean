/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Tactics

/- SizeOf -/

class SizeOf (α : Sort u) where
  sizeOf : α → Nat

export SizeOf (sizeOf)

/-
Declare sizeOf instances and theorems for types declared before SizeOf.
From now on, the inductive Compiler will automatically generate sizeOf instances and theorems.
-/

/- Every Type `α` has a default SizeOf instance that just returns 0 for every element of `α` -/
protected def default.sizeOf (α : Sort u) : α → Nat
  | _ => 0

instance (priority := low) (α : Sort u) : SizeOf α where
  sizeOf := default.sizeOf α

@[simp] theorem sizeOf_default (n : α) : sizeOf n = 0 := rfl

instance : SizeOf Nat where
  sizeOf n := n

@[simp] theorem sizeOf_nat (n : Nat) : sizeOf n = n := rfl

instance [SizeOf α] : SizeOf (Unit → α) where
  sizeOf f := sizeOf (f ())

@[simp] theorem sizeOf_thunk [SizeOf α] (f : Unit → α) : sizeOf f = sizeOf (f ()) :=
  rfl

deriving instance SizeOf for Prod
deriving instance SizeOf for PUnit
deriving instance SizeOf for Bool
deriving instance SizeOf for Option
deriving instance SizeOf for List
deriving instance SizeOf for Array
deriving instance SizeOf for Subtype
deriving instance SizeOf for Fin
deriving instance SizeOf for USize
deriving instance SizeOf for UInt8
deriving instance SizeOf for UInt16
deriving instance SizeOf for UInt32
deriving instance SizeOf for UInt64
deriving instance SizeOf for Char
deriving instance SizeOf for String
deriving instance SizeOf for Substring
deriving instance SizeOf for Except
deriving instance SizeOf for EStateM.Result

@[simp] theorem Unit.sizeOf (u : Unit) : sizeOf u = 1 := rfl
@[simp] theorem Bool.sizeOf_eq_one (b : Bool) : sizeOf b = 1 := by cases b <;> rfl

namespace Lean

/- We manually define `Lean.Name` instance because we use
   an opaque function for computing the hashcode field. -/
protected noncomputable def Name.sizeOf : Name → Nat
  | anonymous => 1
  | str p s   => 1 + Name.sizeOf p + sizeOf s
  | num p n   => 1 + Name.sizeOf p + sizeOf n

noncomputable instance : SizeOf Name where
  sizeOf n := n.sizeOf

@[simp] theorem Name.anonymous.sizeOf_spec : sizeOf anonymous = 1 :=
  rfl
@[simp] theorem Name.str.sizeOf_spec (p : Name) (s : String) : sizeOf (str p s) = 1 + sizeOf p + sizeOf s :=
  rfl
@[simp] theorem Name.num.sizeOf_spec (p : Name) (n : Nat) : sizeOf (num p n) = 1 + sizeOf p + sizeOf n :=
  rfl

deriving instance SizeOf for Syntax

end Lean
