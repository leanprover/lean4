/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint init.data.string
universes u

class hashable (α : Type u) :=
(hash : α → usize)

export hashable (hash)

-- TODO: mark as builtin and opaque
def mixHash (u₁ u₂ : usize) : usize :=
default usize

-- TODO: mark as builtin
protected def string.hash (s : string) : usize :=
default usize

instance : hashable string := ⟨string.hash⟩

-- TODO: add builtin
protected def nat.hash (n : nat) : usize :=
usize.ofNat n

instance : hashable nat := ⟨nat.hash⟩
