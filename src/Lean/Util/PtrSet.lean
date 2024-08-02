/-
Copyright (c) 2023 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Hashable
import Lean.Data.HashSet
import Lean.Data.HashMap

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

/--
Map of pointers. It is a low-level auxiliary datastructure used for traversing DAGs.
-/
unsafe def PtrMap (α : Type) (β : Type) :=
  HashMap (Ptr α) β

unsafe def mkPtrMap {α β : Type} (capacity : Nat := 64) : PtrMap α β :=
  mkHashMap capacity

unsafe abbrev PtrMap.insert (s : PtrMap α β) (a : α) (b : β) : PtrMap α β :=
  HashMap.insert s { value := a } b

unsafe abbrev PtrMap.contains (s : PtrMap α β) (a : α) : Bool :=
  HashMap.contains s { value := a }

unsafe abbrev PtrMap.find? (s : PtrMap α β) (a : α) : Option β :=
  HashMap.find? s { value := a }

end Lean
