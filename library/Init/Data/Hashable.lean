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
constant mixHash (u₁ u₂ : USize) : USize := default _

@[extern "lean_string_hash"]
protected constant String.hash (s : String) : USize := default _
instance : Hashable String := ⟨String.hash⟩

protected def Nat.hash (n : Nat) : USize :=
USize.ofNat n

instance : Hashable Nat := ⟨Nat.hash⟩
