/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt
import Init.Data.String
universes u

class Hashable (α : Type u) :=
(hash : α → USize)

export Hashable (hash)

@[extern "lean_usize_mix_hash"]
constant mixHash (u₁ u₂ : USize) : USize := arbitrary _

@[extern "lean_string_hash"]
protected constant String.hash (s : @& String) : USize := arbitrary _
instance : Hashable String := ⟨String.hash⟩

protected def Nat.hash (n : Nat) : USize :=
USize.ofNat n

instance : Hashable Nat := ⟨Nat.hash⟩

instance {α β} [Hashable α] [Hashable β] : Hashable (α × β) :=
⟨fun ⟨a, b⟩ => mixHash (hash a) (hash b)⟩

def Option.hash {α} [Hashable α] : Option α → USize
| none   => 11
| some a => mixHash (hash a) 13

instance {α} [Hashable α] : Hashable (Option α) := ⟨Option.hash⟩

def List.hash {α} [Hashable α] (as : List α) : USize :=
as.foldl (fun r a => mixHash r (hash a)) 7

instance {α} [Hashable α] : Hashable (List α) := ⟨List.hash⟩
