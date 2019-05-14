/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.hashmap init.data.rbmap
universes u v w w'

namespace Lean

/- Staged map for implementing the Environment. The idea is to store
   imported entries into a hashtable and local entries into a red-black tree.

   Hypotheses:
   - The number of entries (i.e., declarations) coming from imported files is much bigger than
     the number of entries in the current file.
   - HashMap is faster than RBMap.
   - When we are reading imported files, we have exclusive access to the map, and efficient
     destructive updates are performed.

   Remarks:
   - We never remove declarations from the Environment. In principle, we could support
     deletion by using `(RBMap α (Option β) lt)` where the value `none` would indicate
     that an entry was "removed" from the hashtable.
   - We do not need additional bookkeeping for extracting the local entries.
-/
structure SMap (α : Type u) (β : Type v) (lt : α → α → Bool) [HasBeq α] [Hashable α] :=
(stage₁ : Bool         := true)
(map₁   : HashMap α β  := {})
(map₂   : RBMap α β lt := {})

namespace SMap
variables {α : Type u} {β : Type v} {lt : α → α → Bool} [HasBeq α] [Hashable α]

def empty : SMap α β lt := {}
instance : HasEmptyc (SMap α β lt) := ⟨SMap.empty⟩

@[specialize] def insert : SMap α β lt → α → β → SMap α β lt
| ⟨true, m₁, m₂⟩ k v  := ⟨true, m₁.insert k v, m₂⟩
| ⟨false, m₁, m₂⟩ k v := ⟨false, m₁, m₂.insert k v⟩

@[specialize] def find : SMap α β lt → α → Option β
| ⟨true, m₁, _⟩ k   := m₁.find k
| ⟨false, m₁, m₂⟩ k := (m₂.find k).orelse (m₁.find k)

@[specialize] def contains : SMap α β lt → α → Bool
| ⟨true, m₁, _⟩ k   := m₁.contains k
| ⟨false, m₁, m₂⟩ k := m₂.contains k || m₁.contains k

/- Move from stage 1 into stage 2. -/
def switch (m : SMap α β lt) : SMap α β lt :=
if m.stage₁ then { stage₁ := false, .. m } else m

@[inline] def foldStage2 {σ : Type w} (f : σ → α → β → σ) (s : σ) (m : SMap α β lt) : σ :=
m.map₂.fold f s

end SMap
end Lean
