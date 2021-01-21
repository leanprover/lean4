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

instance [SizeOf α] [SizeOf β] : SizeOf (Prod α β) where
  sizeOf
    | (a, b) => 1 + sizeOf a + sizeOf b

instance : SizeOf PUnit where
  sizeOf _ := 1

instance : SizeOf Bool where
  sizeOf _ := 1

instance [SizeOf α] : SizeOf (Option α) where
  sizeOf
    | none   => 1
    | some a => 1 + sizeOf a

protected def List.sizeOf [SizeOf α] : List α → Nat
  | []    => 1
  | x::xs => 1 + sizeOf x + List.sizeOf xs

instance [SizeOf α] : SizeOf (List α) where
  sizeOf xs := xs.sizeOf

instance [SizeOf α] : SizeOf (Array α) where
  sizeOf xs := 1 + sizeOf xs.data

instance [SizeOf α] (p : α → Prop) : SizeOf (Subtype p) where
  sizeOf
    | ⟨a, _⟩ => 1 + sizeOf a

instance [SizeOf ε] [SizeOf α] : SizeOf (Except ε α) where
  sizeOf
    | Except.error e => 1 + sizeOf e
    | Except.ok a    => 1 + sizeOf a

instance [SizeOf ε] [SizeOf σ] [SizeOf α] : SizeOf (EStateM.Result ε σ α) where
  sizeOf
    | EStateM.Result.ok a s    => 1 + sizeOf a + sizeOf s
    | EStateM.Result.error e s => 1 + sizeOf e + sizeOf s

protected def Lean.Name.sizeOf : Name → Nat
  | anonymous => 1
  | str p s _ => 1 + Name.sizeOf p + sizeOf s
  | num p n _ => 1 + Name.sizeOf p + sizeOf n

instance : SizeOf Lean.Name where
  sizeOf n := n.sizeOf
