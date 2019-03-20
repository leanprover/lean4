/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint init.data.string
universes u

class Hashable (α : Type u) :=
(hash : α → Usize)

export Hashable (hash)

-- TODO: mark as builtin and opaque
def mixHash (u₁ u₂ : Usize) : Usize :=
default Usize

-- TODO: mark as builtin
protected def String.hash (s : String) : Usize :=
default Usize

instance : Hashable String := ⟨String.hash⟩

-- TODO: add builtin
protected def Nat.hash (n : Nat) : Usize :=
Usize.ofNat n

instance : Hashable Nat := ⟨Nat.hash⟩
