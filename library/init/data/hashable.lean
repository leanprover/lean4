/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint init.data.string
universes u

class Hashable (α : Type u) :=
(hash : α → USize)

export Hashable (hash)

-- TODO: mark as builtin and opaque
def mixHash (u₁ u₂ : USize) : USize :=
default USize

-- TODO: mark as builtin
protected def String.hash (s : String) : USize :=
default USize

instance : Hashable String := ⟨String.hash⟩

-- TODO: add builtin
protected def Nat.hash (n : Nat) : USize :=
USize.ofNat n

instance : Hashable Nat := ⟨Nat.hash⟩
