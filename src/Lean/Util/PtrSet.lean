/-
Copyright (c) 2023 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.HashSet

namespace Lean

structure Ptr (α : Type u) where
  value : α

unsafe instance : Hashable (Ptr α) where
  hash a := hash64 (ptrAddrUnsafe a).toUInt64

unsafe instance : BEq (Ptr α) where
  beq a b := ptrAddrUnsafe a == ptrAddrUnsafe b

/--
Set of pointers. It is a low-level auxiliary datastructure used for traversing DAGs.
-/
unsafe def PtrSet (α : Type) :=
  HashSet (Ptr α)

unsafe def mkPtrSet {α : Type} (capacity : Nat := 64) : PtrSet α :=
  mkHashSet capacity

unsafe abbrev PtrSet.insert (s : PtrSet α) (a : α) : PtrSet α :=
  HashSet.insert s { value := a }

unsafe abbrev PtrSet.contains (s : PtrSet α) (a : α) : Bool :=
  HashSet.contains s { value := a }

end Lean
