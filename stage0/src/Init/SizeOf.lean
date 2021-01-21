/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Notation

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
  | a => 0

instance (priority := low) (α : Sort u) : SizeOf α where
  sizeOf := default.sizeOf α

instance : SizeOf Nat where
  sizeOf n := n

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

/- We manually define `Lean.Name` instance because we use
   an opaque function for computing the hashcode field. -/
protected noncomputable def Lean.Name.sizeOf : Name → Nat
  | anonymous => 1
  | str p s _ => 1 + Name.sizeOf p + sizeOf s
  | num p n _ => 1 + Name.sizeOf p + sizeOf n

noncomputable instance : SizeOf Lean.Name where
  sizeOf n := n.sizeOf

deriving instance SizeOf for Lean.Syntax
