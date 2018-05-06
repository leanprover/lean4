/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.usize init.data.string
universes u

class hashable (α : Type u) :=
(hash : α → usize)

-- TODO: mark as builtin
def string.hash (s : string) : usize :=
default usize

instance : hashable string :=
⟨string.hash⟩

export hashable (hash)
